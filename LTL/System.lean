import LTL.Soundness

/-!
# Transition systems and their encoding as sequent hypotheses

A finite transition system is given by lists, so that every fact about it can
be checked by `decide`. Its encoding `S.hyps` is a list of LTL formulas over the
extended alphabet `AP ⊕ Q`: atom `inr q` ("at q") says the system is in state `q`.

The main theorem `System.sat_of_derives` says that a sequent derivation of
`S.hyps ⊢ [φ]` establishes `S ⊨ φ`.
-/

namespace LTL

/-- A finite labelled transition system with states `Q` over atoms `AP`. -/
structure System (AP Q : Type) where
  /-- the atoms the labelling talks about -/
  props : List AP
  states : List Q
  init : List Q
  succ : Q → List Q
  /-- the atoms true in a state -/
  label : Q → List AP

namespace System

variable {AP Q : Type} (S : System AP Q)

/-- An execution: starts in an initial state and follows transitions forever. -/
structure IsExec (π : Nat → Q) : Prop where
  start : π 0 ∈ S.init
  step : ∀ n, π (n + 1) ∈ S.succ (π n)

/-- The trace of an execution. -/
def traceOf (π : Nat → Q) : Trace AP := fun n p => p ∈ S.label (π n)

/-- `S ⊨ φ`: every trace of `S` satisfies `φ` at position 0. -/
def Models (φ : Formula AP) : Prop :=
  ∀ π, S.IsExec π → Sat (S.traceOf π) 0 φ

/-! ## The encoding -/

/-- The atom "the system is in state `q`". -/
def at_ (q : Q) : Formula (AP ⊕ Q) := .atom (.inr q)

/-- An atom of the specification, moved to the extended alphabet. -/
def ap (p : AP) : Formula (AP ⊕ Q) := .atom (.inl p)

/-- A specification, moved to the extended alphabet. -/
def lift (φ : Formula AP) : Formula (AP ⊕ Q) := φ.map .inl

variable [DecidableEq AP]

/-- Facts about one state `q`, each wrapped in `G`:
labels that hold, labels that fail, and the possible next states. -/
def stateHyps (q : Q) : List (Formula (AP ⊕ Q)) :=
  (S.label q).map (fun p => 𝐆 (at_ q ⇒ ap p)) ++
  ((S.props.filter fun p => p ∉ S.label q).map fun p => 𝐆 (at_ q ⇒ ∼(ap p))) ++
  [𝐆 (at_ q ⇒ 𝐗 (Formula.bigOr ((S.succ q).map at_)))]

/-- The hypotheses `Γ_S` describing `S`. -/
def hyps : List (Formula (AP ⊕ Q)) :=
  Formula.bigOr (S.init.map at_) :: S.states.flatMap S.stateHyps

/-! ## Correctness of the encoding -/

/-- The extended trace of an execution: the original atoms, plus "at `π n`". -/
def extTrace (π : Nat → Q) : Trace (AP ⊕ Q)
  | n, .inl p => p ∈ S.label (π n)
  | n, .inr q => q = π n

/-- Every execution's extended trace satisfies all of `Γ_S` at position 0. -/
theorem hyps_hold {π : Nat → Q} (hπ : S.IsExec π) :
    ∀ A ∈ S.hyps, Sat (S.extTrace π) 0 A := by
  intro A hA
  simp only [hyps, List.mem_cons, List.mem_flatMap] at hA
  rcases hA with rfl | ⟨q, -, hA⟩
  · rw [sat_bigOr]
    exact ⟨at_ (π 0), List.mem_map_of_mem hπ.start, rfl⟩
  · simp only [stateHyps, List.mem_append, List.mem_map, List.mem_filter,
      List.mem_singleton] at hA
    rcases hA with (⟨p, hp, rfl⟩ | ⟨p, ⟨-, hp⟩, rfl⟩) | rfl
    · intro j _ hq
      change q = π j at hq
      subst hq
      exact hp
    · intro j _ hq
      change q = π j at hq
      subst hq
      exact fun h => by simp at hp; exact hp h
    · intro j _ hq
      change q = π j at hq
      subst hq
      rw [Sat, sat_bigOr]
      exact ⟨at_ (π (j + 1)), List.mem_map_of_mem (hπ.step j), rfl⟩

/-- **End-to-end soundness.** A derivation of `Γ_S ⊢ φ` proves `S ⊨ φ`. -/
theorem sat_of_derives {φ : Formula AP} (h : S.hyps ⊢ [lift φ]) :
    S.Models φ := by
  intro π hπ
  obtain ⟨B, hB, hs⟩ := soundness h (S.extTrace π) 0 (S.hyps_hold hπ)
  simp only [List.mem_singleton] at hB
  subst hB
  rw [lift, sat_map] at hs
  exact hs

end System

end LTL
