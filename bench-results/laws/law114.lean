import LTL

open LTL

-- LTL law 114: □ p ⟹ (□ q ⇒ □ (p ⇒ q))
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐆 (q) ⇒ 𝐆 ((p ⇒ q)))] := by
  apply Derives.impR (A := 𝐆 q) (B := 𝐆 (p ⇒ q)) (by simp)
  apply Derives.alwaysR (A := p ⇒ q) (I := 𝐆 q) (by simp)
  · exact Derives.ax (A := 𝐆 q) (by simp) (by simp)
  · exact Derives.alwaysL (A := q) (by simp)
      (Derives.ax (A := 𝐗 (𝐆 q)) (by simp) (by simp))
  · exact Derives.impR (A := p) (B := q) (by simp)
      (Derives.alwaysL (A := q) (by simp)
        (Derives.ax (A := q) (by simp) (by simp)))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐆 (q) ⇒ 𝐆 ((p ⇒ q)))] :=
  Candidate.candidate p q

#print axioms verified
