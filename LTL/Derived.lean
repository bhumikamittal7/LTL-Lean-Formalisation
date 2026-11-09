import LTL.Sequent

/-!
# Derived rules

Each rule here is proved from the primitive rules of `Derives`, so using it adds nothing
to what has to be trusted.

* `wk`: weakening is admissible;
* `step`: the `next` rule for a single formula on the right;
* `close`: `ax` with the membership check done by `decide`;
* `topR`, `orL`, `orR`, `evL`, `evR`: rules for the abbreviations `⊤`, `∨`, `F`.
-/

namespace LTL

variable {AP : Type}

/-- Two formulas are interderivable. -/
def Interderivable (A B : Formula AP) : Prop := ([A] ⊢ [B]) ∧ ([B] ⊢ [A])

scoped infix:10 " ⊣⊢ " => Interderivable

namespace Derives

private theorem cons_sub {A : Formula AP} {Γ Γ' : List (Formula AP)}
    (h : ∀ x ∈ Γ, x ∈ Γ') : ∀ x ∈ A :: Γ, x ∈ A :: Γ' := by
  intro x hx
  simp only [List.mem_cons] at hx ⊢
  exact hx.imp_right (h x)

/-- Weakening: more hypotheses and more conclusions keep a sequent derivable. -/
theorem wk {Γ Δ Γ' Δ' : List (Formula AP)} (h : Γ ⊢ Δ)
    (hΓ : ∀ x ∈ Γ, x ∈ Γ') (hΔ : ∀ x ∈ Δ, x ∈ Δ') : Γ' ⊢ Δ' := by
  induction h generalizing Γ' Δ' with
  | ax h1 h2 => exact ax (hΓ _ h1) (hΔ _ h2)
  | botL h1 => exact botL (hΓ _ h1)
  | negL h1 _ ih => exact negL (hΓ _ h1) (ih hΓ (cons_sub hΔ))
  | negR h1 _ ih => exact negR (hΔ _ h1) (ih (cons_sub hΓ) hΔ)
  | andL h1 _ ih => exact andL (hΓ _ h1) (ih (cons_sub (cons_sub hΓ)) hΔ)
  | andR h1 _ _ ih1 ih2 => exact andR (hΔ _ h1) (ih1 hΓ (cons_sub hΔ)) (ih2 hΓ (cons_sub hΔ))
  | impL h1 _ _ ih1 ih2 => exact impL (hΓ _ h1) (ih1 hΓ (cons_sub hΔ)) (ih2 (cons_sub hΓ) hΔ)
  | impR h1 _ ih => exact impR (hΔ _ h1) (ih (cons_sub hΓ) (cons_sub hΔ))
  | cut A _ _ ih1 ih2 => exact cut A (ih1 hΓ (cons_sub hΔ)) (ih2 (cons_sub hΓ) hΔ)
  | next h h1 h2 _ => exact next h (fun A hA => hΓ _ (h1 A hA)) (fun B hB => hΔ _ (h2 B hB))
  | alwaysL h1 _ ih => exact alwaysL (hΓ _ h1) (ih (cons_sub (cons_sub hΓ)) hΔ)
  | alwaysR I h1 _ h3 h4 ih => exact alwaysR I (hΔ _ h1) (ih hΓ (cons_sub hΔ)) h3 h4
  | untilL I h1 h2 h3 _ _ _ ih => exact untilL I (hΓ _ h1) h2 h3 (ih (cons_sub hΓ) hΔ)
  | untilR h1 _ _ ih1 ih2 =>
    exact untilR (hΔ _ h1) (ih1 hΓ (cons_sub (cons_sub hΔ))) (ih2 hΓ (cons_sub (cons_sub hΔ)))

/-- The `next` rule for one formula on the right: from `A₁, …, Aₙ ⊢ B`, and
`X A₁, …, X Aₙ` among the hypotheses, conclude any sequent with `X B` on the right. -/
theorem step {Γ Δ Γ' : List (Formula AP)} {B : Formula AP} (h : Γ' ⊢ [B])
    (hΓ : ∀ A ∈ Γ', 𝐗 A ∈ Γ) (hB : 𝐗 B ∈ Δ) : Γ ⊢ Δ :=
  next h hΓ (by simpa using hB)

/-- Close a sequent that has a formula on both sides; `by decide` checks this
on concrete sequents. -/
theorem close [DecidableEq AP] {Γ Δ : List (Formula AP)}
    (h : (Γ.any fun A => Δ.contains A) = true) : Γ ⊢ Δ := by
  obtain ⟨A, hA, hc⟩ := List.any_eq_true.mp h
  exact ax hA (List.contains_iff_mem.mp hc)

/-- `Γ ⊢ ⊤, Δ` -/
theorem topR {Γ Δ : List (Formula AP)} (h : ⊤ₗ ∈ Δ) : Γ ⊢ Δ :=
  negR (A := ⊥ₗ) h (botL (by simp))

/-- from `Γ, A ⊢ Δ` and `Γ, B ⊢ Δ` infer `Γ, A ∨ B ⊢ Δ` -/
theorem orL {Γ Δ : List (Formula AP)} {A B : Formula AP} (h : (A ⋎ B) ∈ Γ)
    (h1 : A :: Γ ⊢ Δ) (h2 : B :: Γ ⊢ Δ) : Γ ⊢ Δ :=
  impL (A := ∼A) (B := B) h (negR (A := A) (by simp) (wk h1 (fun _ h => h) (by simp_all))) h2

/-- from `Γ ⊢ A, B, Δ` infer `Γ ⊢ A ∨ B, Δ` -/
theorem orR {Γ Δ : List (Formula AP)} {A B : Formula AP} (h : (A ⋎ B) ∈ Δ)
    (h1 : Γ ⊢ A :: B :: Δ) : Γ ⊢ Δ :=
  impR (A := ∼A) (B := B) h (negL (A := A) (by simp) (wk h1 (by simp_all) (by simp_all)))

/-- from `Γ ⊢ A, X F A, Δ` infer `Γ ⊢ F A, Δ` -/
theorem evR {Γ Δ : List (Formula AP)} {A : Formula AP} (h : (𝐅 A) ∈ Δ)
    (h1 : Γ ⊢ A :: 𝐗 (𝐅 A) :: Δ) : Γ ⊢ Δ :=
  untilR (A := ⊤ₗ) (B := A) h (topR (by simp)) h1

/-- from `A ⊢ I` and `X I ⊢ I` and `Γ, I ⊢ Δ` infer `Γ, F A ⊢ Δ` -/
theorem evL {Γ Δ : List (Formula AP)} {A : Formula AP} (I : Formula AP) (h : (𝐅 A) ∈ Γ)
    (h1 : [A] ⊢ [I]) (h2 : [𝐗 I] ⊢ [I]) (h3 : I :: Γ ⊢ Δ) : Γ ⊢ Δ :=
  untilL (A := ⊤ₗ) (B := A) I h h1 (wk h2 (by simp) (fun _ h => h)) h3

end Derives

end LTL
