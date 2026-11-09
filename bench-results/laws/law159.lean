import LTL

open LTL

-- LTL law 159: □ ◇ (p ∧ q) ⟹ □ ◇ p ∧ □ ◇ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem evAndLeft {AP : Type} (p q : Formula AP) : [𝐅 (p ⋏ q)] ⊢ [𝐅 p] :=
  Derives.evL (A := p ⋏ q) (I := 𝐅 p) (by simp)
    (Derives.evR (A := p) (by simp)
      (Derives.andL (A := p) (B := q) (by simp)
        (Derives.ax (A := p) (by simp) (by simp))))
    (Derives.evR (A := p) (by simp)
      (Derives.ax (A := 𝐗 (𝐅 p)) (by simp) (by simp)))
    (Derives.ax (A := 𝐅 p) (by simp) (by simp))

theorem evAndRight {AP : Type} (p q : Formula AP) : [𝐅 (p ⋏ q)] ⊢ [𝐅 q] :=
  Derives.evL (A := p ⋏ q) (I := 𝐅 q) (by simp)
    (Derives.evR (A := q) (by simp)
      (Derives.andL (A := p) (B := q) (by simp)
        (Derives.ax (A := q) (by simp) (by simp))))
    (Derives.evR (A := q) (by simp)
      (Derives.ax (A := 𝐗 (𝐅 q)) (by simp) (by simp)))
    (Derives.ax (A := 𝐅 q) (by simp) (by simp))

theorem gfLift {AP : Type} (A B : Formula AP) (h : [𝐅 A] ⊢ [𝐅 B])
    (Δ : List (Formula AP)) (hΔ : 𝐆 (𝐅 B) ∈ Δ) : [𝐆 (𝐅 A)] ⊢ Δ :=
  Derives.alwaysR (A := 𝐅 B) (I := 𝐆 (𝐅 A)) hΔ
    (Derives.ax (A := 𝐆 (𝐅 A)) (by simp) (by simp))
    (Derives.alwaysL (A := 𝐅 A) (by simp)
      (Derives.ax (A := 𝐗 (𝐆 (𝐅 A))) (by simp) (by simp)))
    (Derives.alwaysL (A := 𝐅 A) (by simp)
      (Derives.wk h (by simp) (by simp)))

theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (𝐅 ((p ⋏ q)))] ⊢ [(𝐆 (𝐅 (p)) ⋏ 𝐆 (𝐅 (q)))] :=
  Derives.andR (A := 𝐆 (𝐅 p)) (B := 𝐆 (𝐅 q)) (by simp)
    (gfLift (p ⋏ q) p (evAndLeft p q) _ (by simp))
    (gfLift (p ⋏ q) q (evAndRight p q) _ (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (𝐅 ((p ⋏ q)))] ⊢ [(𝐆 (𝐅 (p)) ⋏ 𝐆 (𝐅 (q)))] :=
  Candidate.candidate p q

#print axioms verified
