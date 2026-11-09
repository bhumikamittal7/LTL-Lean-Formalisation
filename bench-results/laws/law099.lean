import LTL

open LTL

-- LTL law 99: □ (p ∧ q) ≈ □ p ∧ □ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([𝐆 ((p ⋏ q))] ⊢ [(𝐆 (p) ⋏ 𝐆 (q))]) ∧ ([(𝐆 (p) ⋏ 𝐆 (q))] ⊢ [𝐆 ((p ⋏ q))]) := by
  constructor
  · exact Derives.andR (A := 𝐆 p) (B := 𝐆 q) (by simp)
      (Derives.alwaysR (A := p) (I := 𝐆 (p ⋏ q)) (by simp)
        (Derives.ax (A := 𝐆 (p ⋏ q)) (by simp) (by simp))
        (Derives.alwaysL (A := p ⋏ q) (by simp)
          (Derives.ax (A := 𝐗 (𝐆 (p ⋏ q))) (by simp) (by simp)))
        (Derives.alwaysL (A := p ⋏ q) (by simp)
          (Derives.andL (A := p) (B := q) (by simp)
            (Derives.ax (A := p) (by simp) (by simp)))))
      (Derives.alwaysR (A := q) (I := 𝐆 (p ⋏ q)) (by simp)
        (Derives.ax (A := 𝐆 (p ⋏ q)) (by simp) (by simp))
        (Derives.alwaysL (A := p ⋏ q) (by simp)
          (Derives.ax (A := 𝐗 (𝐆 (p ⋏ q))) (by simp) (by simp)))
        (Derives.alwaysL (A := p ⋏ q) (by simp)
          (Derives.andL (A := p) (B := q) (by simp)
            (Derives.ax (A := q) (by simp) (by simp)))))
  · exact Derives.alwaysR (A := p ⋏ q) (I := 𝐆 p ⋏ 𝐆 q) (by simp)
      (Derives.ax (A := 𝐆 p ⋏ 𝐆 q) (by simp) (by simp))
      (Derives.andL (A := 𝐆 p) (B := 𝐆 q) (by simp)
        (Derives.alwaysL (A := p) (by simp)
          (Derives.alwaysL (A := q) (by simp)
            (Derives.step (Γ' := [𝐆 p, 𝐆 q]) (B := 𝐆 p ⋏ 𝐆 q)
              (Derives.andR (A := 𝐆 p) (B := 𝐆 q) (by simp)
                (Derives.ax (A := 𝐆 p) (by simp) (by simp))
                (Derives.ax (A := 𝐆 q) (by simp) (by simp)))
              (by simp) (by simp)))))
      (Derives.andL (A := 𝐆 p) (B := 𝐆 q) (by simp)
        (Derives.alwaysL (A := p) (by simp)
          (Derives.alwaysL (A := q) (by simp)
            (Derives.andR (A := p) (B := q) (by simp)
              (Derives.ax (A := p) (by simp) (by simp))
              (Derives.ax (A := q) (by simp) (by simp))))))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([𝐆 ((p ⋏ q))] ⊢ [(𝐆 (p) ⋏ 𝐆 (q))]) ∧ ([(𝐆 (p) ⋏ 𝐆 (q))] ⊢ [𝐆 ((p ⋏ q))]) :=
  Candidate.candidate p q

#print axioms verified
