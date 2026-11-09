import LTL.Syntax

/-!
# LTL semantics

A trace assigns to each position the set of atoms true there, given as a
predicate. Satisfaction is defined at every position, not only at 0, because the
`X` rule of the sequent calculus moves from position `i` to `i + 1`.
-/

namespace LTL

/-- An infinite trace: `σ i p` says that atom `p` holds at position `i`. -/
def Trace (AP : Type) := Nat → AP → Prop

variable {AP AP' : Type}

/-- `Sat σ i φ`: formula `φ` holds at position `i` of trace `σ`. -/
def Sat (σ : Trace AP) : Nat → Formula AP → Prop
  | i, .atom p => σ i p
  | _, .bot => False
  | i, .neg φ => ¬ Sat σ i φ
  | i, .and φ ψ => Sat σ i φ ∧ Sat σ i ψ
  | i, .imp φ ψ => Sat σ i φ → Sat σ i ψ
  | i, .next φ => Sat σ (i + 1) φ
  | i, .always φ => ∀ j, i ≤ j → Sat σ j φ
  | i, .until φ ψ => ∃ j, i ≤ j ∧ Sat σ j ψ ∧ ∀ k, i ≤ k → k < j → Sat σ k φ

/-- Satisfaction of a renamed formula only looks at the renamed atoms. -/
theorem sat_map (f : AP → AP') (τ : Trace AP') :
    ∀ (φ : Formula AP) (i : Nat), Sat τ i (φ.map f) ↔ Sat (fun n p => τ n (f p)) i φ
  | .atom _, _ => Iff.rfl
  | .bot, _ => Iff.rfl
  | .neg φ, i => by simp only [Formula.map, Sat, sat_map f τ φ i]
  | .and φ ψ, i => by simp only [Formula.map, Sat, sat_map f τ φ i, sat_map f τ ψ i]
  | .imp φ ψ, i => by simp only [Formula.map, Sat, sat_map f τ φ i, sat_map f τ ψ i]
  | .next φ, i => by simp only [Formula.map, Sat, sat_map f τ φ (i + 1)]
  | .always φ, i => by simp only [Formula.map, Sat, sat_map f τ φ]
  | .until φ ψ, i => by simp only [Formula.map, Sat, sat_map f τ φ, sat_map f τ ψ]

/-! ## The abbreviations -/

@[simp] theorem sat_top (σ : Trace AP) (i : Nat) : Sat σ i (Formula.top : Formula AP) :=
  fun h => h

@[simp] theorem sat_or (σ : Trace AP) (i : Nat) (φ ψ : Formula AP) :
    Sat σ i (Formula.or φ ψ) ↔ Sat σ i φ ∨ Sat σ i ψ := by
  simp only [Formula.or, Sat]
  exact ⟨fun h => (Classical.em _).elim .inl fun hn => .inr (h hn),
    fun h hn => h.resolve_left hn⟩

@[simp] theorem sat_eventually (σ : Trace AP) (i : Nat) (φ : Formula AP) :
    Sat σ i (Formula.eventually φ) ↔ ∃ j, i ≤ j ∧ Sat σ j φ := by
  simp only [Formula.eventually, Sat]
  exact ⟨fun ⟨j, h1, h2, _⟩ => ⟨j, h1, h2⟩, fun ⟨j, h1, h2⟩ => ⟨j, h1, h2, fun _ _ _ h => h⟩⟩

theorem sat_bigOr (σ : Trace AP) (i : Nat) :
    ∀ (φs : List (Formula AP)), Sat σ i (Formula.bigOr φs) ↔ ∃ φ ∈ φs, Sat σ i φ
  | [] => by simp [Formula.bigOr, Sat]
  | φ :: φs => by simp [Formula.bigOr, sat_or, sat_bigOr σ i φs]

end LTL
