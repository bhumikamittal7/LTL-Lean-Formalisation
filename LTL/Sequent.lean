import LTL.Semantics

/-!
# The proof system

A sequent `Γ ⊢ Δ` has lists of formulas on both sides and reads "if all of `Γ`
hold, then some formula of `Δ` holds". The rules:

* axioms: `ax`, `botL`;
* propositional rules of Gentzen's LK, for `¬ ∧ →`: `negL negR andL andR impL impR`;
* `cut`;
* next: `next` (from `Γ ⊢ Δ` infer `X Γ ⊢ X Δ`, with weakening built in);
* always: `alwaysL` (unfold `G A` into `A` and `X G A`) and `alwaysR` (induction
  with an invariant `I`);
* until: `untilL` (induction with an invariant `I`) and `untilR` (unfold).

`alwaysR` is the induction rule of Kröger and Merz, *Temporal Logic and State
Systems* (Springer, 2008), Ch. 2, written as a sequent rule. `untilL` is
induction for least fixpoints (Kozen, 1983), applied to `A U B`.

A rule names its principal formula by membership and keeps it in the premise;
this builds in exchange and contraction. Weakening is admissible
(`Derives.wk` in `LTL/Derived.lean`).
-/

namespace LTL

variable {AP : Type}

inductive Derives : List (Formula AP) → List (Formula AP) → Prop
  /-- `Γ, A ⊢ A, Δ` -/
  | ax {Γ Δ A} : A ∈ Γ → A ∈ Δ → Derives Γ Δ
  /-- `Γ, ⊥ ⊢ Δ` -/
  | botL {Γ Δ} : ⊥ₗ ∈ Γ → Derives Γ Δ
  /-- from `Γ ⊢ A, Δ` infer `Γ, ¬A ⊢ Δ` -/
  | negL {Γ Δ A} : (∼A) ∈ Γ → Derives Γ (A :: Δ) → Derives Γ Δ
  /-- from `Γ, A ⊢ Δ` infer `Γ ⊢ ¬A, Δ` -/
  | negR {Γ Δ A} : (∼A) ∈ Δ → Derives (A :: Γ) Δ → Derives Γ Δ
  /-- from `Γ, A, B ⊢ Δ` infer `Γ, A ∧ B ⊢ Δ` -/
  | andL {Γ Δ A B} : (A ⋏ B) ∈ Γ → Derives (A :: B :: Γ) Δ → Derives Γ Δ
  /-- from `Γ ⊢ A, Δ` and `Γ ⊢ B, Δ` infer `Γ ⊢ A ∧ B, Δ` -/
  | andR {Γ Δ A B} : (A ⋏ B) ∈ Δ → Derives Γ (A :: Δ) → Derives Γ (B :: Δ) → Derives Γ Δ
  /-- from `Γ ⊢ A, Δ` and `Γ, B ⊢ Δ` infer `Γ, A → B ⊢ Δ` -/
  | impL {Γ Δ A B} : (A ⇒ B) ∈ Γ → Derives Γ (A :: Δ) → Derives (B :: Γ) Δ → Derives Γ Δ
  /-- from `Γ, A ⊢ B, Δ` infer `Γ ⊢ A → B, Δ` -/
  | impR {Γ Δ A B} : (A ⇒ B) ∈ Δ → Derives (A :: Γ) (B :: Δ) → Derives Γ Δ
  /-- from `Γ ⊢ A, Δ` and `Γ, A ⊢ Δ` infer `Γ ⊢ Δ` -/
  | cut {Γ Δ} (A : Formula AP) : Derives Γ (A :: Δ) → Derives (A :: Γ) Δ → Derives Γ Δ
  /-- from `Γ' ⊢ Δ'` infer `Σ, X Γ' ⊢ X Δ', Π` -/
  | next {Γ Δ Γ' Δ'} : Derives Γ' Δ' →
      (∀ A ∈ Γ', 𝐗 A ∈ Γ) → (∀ B ∈ Δ', 𝐗 B ∈ Δ) → Derives Γ Δ
  /-- from `Γ, A, X G A ⊢ Δ` infer `Γ, G A ⊢ Δ` -/
  | alwaysL {Γ Δ A} : (𝐆 A) ∈ Γ → Derives (A :: 𝐗 (𝐆 A) :: Γ) Δ → Derives Γ Δ
  /-- from `Γ ⊢ I, Δ` and `I ⊢ X I` and `I ⊢ A` infer `Γ ⊢ G A, Δ` -/
  | alwaysR {Γ Δ A} (I : Formula AP) : (𝐆 A) ∈ Δ →
      Derives Γ (I :: Δ) → Derives [I] [𝐗 I] → Derives [I] [A] → Derives Γ Δ
  /-- from `B ⊢ I` and `A, X I ⊢ I` and `Γ, I ⊢ Δ` infer `Γ, A U B ⊢ Δ` -/
  | untilL {Γ Δ A B} (I : Formula AP) : (A 𝐔 B) ∈ Γ →
      Derives [B] [I] → Derives [A, 𝐗 I] [I] → Derives (I :: Γ) Δ → Derives Γ Δ
  /-- from `Γ ⊢ B, A, Δ` and `Γ ⊢ B, X (A U B), Δ` infer `Γ ⊢ A U B, Δ` -/
  | untilR {Γ Δ A B} : (A 𝐔 B) ∈ Δ →
      Derives Γ (B :: A :: Δ) → Derives Γ (B :: 𝐗 (A 𝐔 B) :: Δ) → Derives Γ Δ

scoped infix:10 " ⊢ " => Derives

/-- Semantic validity of a sequent, at every position of every trace. -/
def SValid (Γ Δ : List (Formula AP)) : Prop :=
  ∀ (σ : Trace AP) (i : Nat), (∀ A ∈ Γ, Sat σ i A) → ∃ B ∈ Δ, Sat σ i B

end LTL
