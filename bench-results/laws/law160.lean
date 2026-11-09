import LTL

open LTL

-- LTL law 160: ◇ □ p ∨ ◇ □ q ⟹ ◇ □ (p ∨ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem fg_mono {AP : Type} (p r : Formula AP) (h : [p] ⊢ [r]) :
    [𝐅 (𝐆 p)] ⊢ [𝐅 (𝐆 r)] :=
  Derives.evL (A := 𝐆 p) (𝐅 (𝐆 r)) (by simp)
    (Derives.evR (A := 𝐆 r) (by simp)
      (Derives.alwaysR (A := r) (𝐆 p) (by simp)
        (Derives.ax (A := 𝐆 p) (by simp) (by simp))
        (Derives.alwaysL (A := p) (by simp)
          (Derives.ax (A := 𝐗 (𝐆 p)) (by simp) (by simp)))
        (Derives.alwaysL (A := p) (by simp)
          (Derives.wk h (by simp) (by simp)))))
    (Derives.evR (A := 𝐆 r) (by simp)
      (Derives.ax (A := 𝐗 (𝐅 (𝐆 r))) (by simp) (by simp)))
    (Derives.ax (A := 𝐅 (𝐆 r)) (by simp) (by simp))

theorem candidate {AP : Type} (p q : Formula AP) :
    [(𝐅 (𝐆 (p)) ⋎ 𝐅 (𝐆 (q)))] ⊢ [𝐅 (𝐆 ((p ⋎ q)))] :=
  Derives.orL (A := 𝐅 (𝐆 p)) (B := 𝐅 (𝐆 q)) (by simp)
    (Derives.wk
      (fg_mono p (p ⋎ q)
        (Derives.orR (A := p) (B := q) (by simp)
          (Derives.ax (A := p) (by simp) (by simp))))
      (by simp) (by simp))
    (Derives.wk
      (fg_mono q (p ⋎ q)
        (Derives.orR (A := p) (B := q) (by simp)
          (Derives.ax (A := q) (by simp) (by simp))))
      (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [(𝐅 (𝐆 (p)) ⋎ 𝐅 (𝐆 (q)))] ⊢ [𝐅 (𝐆 ((p ⋎ q)))] :=
  Candidate.candidate p q

#print axioms verified
