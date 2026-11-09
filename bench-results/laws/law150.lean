import LTL

open LTL

-- LTL law 150: □ p ⟹ (□ q ⇒ □ (p U q))
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐆 (q) ⇒ 𝐆 ((p 𝐔 q)))] := by
  exact Derives.impR (A := 𝐆 q) (B := 𝐆 (p 𝐔 q)) (by simp)
    (Derives.alwaysR (A := p 𝐔 q) (I := 𝐆 q) (by simp)
      (Derives.ax (A := 𝐆 q) (by simp) (by simp))
      (Derives.alwaysL (A := q) (by simp)
        (Derives.ax (A := 𝐗 (𝐆 q)) (by simp) (by simp)))
      (Derives.alwaysL (A := q) (by simp)
        (Derives.untilR (A := p) (B := q) (by simp)
          (Derives.ax (A := q) (by simp) (by simp))
          (Derives.ax (A := q) (by simp) (by simp)))))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐆 (q) ⇒ 𝐆 ((p 𝐔 q)))] :=
  Candidate.candidate p q

#print axioms verified
