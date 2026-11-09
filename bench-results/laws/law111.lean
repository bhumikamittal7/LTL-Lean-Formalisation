import LTL

open LTL

-- LTL law 111: □ p ⟹ (□ q ⇒ □ (p ∨ q))
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐆 (q) ⇒ 𝐆 ((p ⋎ q)))] := by
  exact Derives.impR (A := 𝐆 q) (B := 𝐆 (p ⋎ q)) (by simp)
    (Derives.alwaysR (A := p ⋎ q) (I := 𝐆 p) (by simp)
      (Derives.ax (A := 𝐆 p) (by simp) (by simp))
      (Derives.alwaysL (A := p) (by simp)
        (Derives.ax (A := 𝐗 (𝐆 p)) (by simp) (by simp)))
      (Derives.orR (A := p) (B := q) (by simp)
        (Derives.alwaysL (A := p) (by simp)
          (Derives.ax (A := p) (by simp) (by simp)))))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐆 (q) ⇒ 𝐆 ((p ⋎ q)))] :=
  Candidate.candidate p q

#print axioms verified
