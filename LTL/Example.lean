import LTL.System
import LTL.Derived

/-!
# Running example

A process waits for one step and is then done forever:

    → q₀ {wait} ⟶ q₁ {done} ⟲

We prove `S ⊨ F G done` by a sequent derivation of `Γ_S ⊢ F G done`. The only
creative input is the invariant `I` for the `G` rule; the other steps follow
the shape of the goal.
-/

namespace LTL.Example

inductive P where
  | wait
  | done
  deriving DecidableEq, Repr

inductive St where
  | q0
  | q1
  deriving DecidableEq, Repr

open P St LTL.System

/-- The running example. -/
def S : System P St where
  props := [wait, done]
  states := [q0, q1]
  init := [q0]
  succ
    | q0 => [q1]
    | q1 => [q1]
  label
    | q0 => [wait]
    | q1 => [done]

/-- The specification: from some point on, always done. -/
def spec : Formula P := 𝐅 (𝐆 (.atom done))

/-! ## The hypotheses `Γ_S`, spelled out -/

abbrev A0 : Formula (P ⊕ St) := at_ q0
abbrev A1 : Formula (P ⊕ St) := at_ q1
abbrev Done : Formula (P ⊕ St) := ap done
/-- `X` of the successor disjunction of `q₀` and of `q₁` (both are `at q₁ ∨ ⊥`). -/
abbrev N1 : Formula (P ⊕ St) := A1 ⋎ ⊥ₗ
abbrev T0 : Formula (P ⊕ St) := 𝐆 (A0 ⇒ 𝐗 N1)
abbrev T1 : Formula (P ⊕ St) := 𝐆 (A1 ⇒ 𝐗 N1)
abbrev D1 : Formula (P ⊕ St) := 𝐆 (A1 ⇒ Done)

theorem hyps_eq : S.hyps =
    [A0 ⋎ ⊥ₗ,
     𝐆 (A0 ⇒ ap wait), 𝐆 (A0 ⇒ ∼(ap done)), T0,
     D1, 𝐆 (A1 ⇒ ∼(ap wait)), T1] := by
  rfl

/-! ## The derivation

Read bottom-up, it follows the informal argument:
unfold `F`, step to position 1 (where the system is in `q₁`), unfold `F` again,
and prove `G done` with the invariant `I`. The `G` rule leaves three
obligations, `ob1`–`ob3`. No cut is used.
-/

/-- The invariant: in `q₁`, together with the two facts about `q₁` that we need. -/
abbrev I : Formula (P ⊕ St) := N1 ⋏ (T1 ⋏ D1)

/-- Unpack the invariant on the left. -/
theorem useI {Δ : List (Formula (P ⊕ St))}
    (h : [N1, T1, D1, T1 ⋏ D1, I] ⊢ Δ) : [I] ⊢ Δ :=
  .andL (A := N1) (B := T1 ⋏ D1) (by simp)
    (.andL (A := T1) (B := D1) (by simp) (.wk h (by simp) (by simp)))

/-- Obligation 1: the invariant holds now. -/
theorem ob1 {Δ : List (Formula (P ⊕ St))} : [N1, T1, D1] ⊢ I :: Δ :=
  .andR (A := N1) (B := T1 ⋏ D1) (by simp) (.ax (A := N1) (by simp) (by simp))
    (.andR (A := T1) (B := D1) (by simp) (.ax (A := T1) (by simp) (by simp))
      (.ax (A := D1) (by simp) (by simp)))

/-- Obligation 2: one step preserves the invariant. -/
theorem ob2 : [I] ⊢ [𝐗 I] :=
  useI <|
  .alwaysL (A := A1 ⇒ 𝐗 N1) (by simp) <|
  .alwaysL (A := A1 ⇒ Done) (by simp) <|
  .orL (A := A1) (B := ⊥ₗ) (by simp)
    (.impL (A := A1) (B := 𝐗 N1) (by simp) (.close (by decide))
      (Derives.step (Γ' := [N1, T1, D1]) (ob1 (Δ := [])) (by simp) (by simp)))
    (.botL (by simp))

/-- Obligation 3: the invariant implies `done`. -/
theorem ob3 : [I] ⊢ [Done] :=
  useI <|
  .alwaysL (A := A1 ⇒ Done) (by simp) <|
  .orL (A := A1) (B := ⊥ₗ) (by simp)
    (.impL (A := A1) (B := Done) (by simp) (.close (by decide)) (.close (by decide)))
    (.botL (by simp))

/-- At position 1: `F G done`, by the `G` rule with invariant `I`. -/
theorem fromQ1 : [N1, T1, D1] ⊢ [lift spec] :=
  .evR (A := 𝐆 Done) (by decide) <|
  .alwaysR (A := Done) I (by simp) ob1 ob2 ob3

/-- The full derivation of `Γ_S ⊢ F G done`. -/
theorem derivation : S.hyps ⊢ [lift spec] := by
  rw [hyps_eq]
  exact
    .evR (A := 𝐆 Done) (by decide) <|
    .orL (A := A0) (B := ⊥ₗ) (by simp)
      (.alwaysL (A := A0 ⇒ 𝐗 N1) (by simp) <|
       .alwaysL (A := A1 ⇒ 𝐗 N1) (by simp) <|
       .alwaysL (A := A1 ⇒ Done) (by simp) <|
       .impL (A := A0) (B := 𝐗 N1) (by simp) (.close (by decide)) <|
       Derives.step (Γ' := [N1, T1, D1]) fromQ1 (by simp) (by decide))
      (.botL (by simp))

/-- **The running example is verified:** every trace of `S` satisfies `F G done`. -/
theorem S_models_spec : S.Models spec :=
  S.sat_of_derives derivation

end LTL.Example
