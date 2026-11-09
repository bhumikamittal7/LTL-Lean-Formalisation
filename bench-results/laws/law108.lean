import LTL

open LTL

-- LTL law 108: □ p ⟹ (□ q ⇒ □ (p ∧ q))
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐆 (q) ⇒ 𝐆 ((p ⋏ q)))] := by
  refine Derives.impR (A := 𝐆 q) (B := 𝐆 (p ⋏ q)) (by simp) ?_
  refine Derives.alwaysR (A := p ⋏ q) (I := (𝐆 p) ⋏ (𝐆 q)) (by simp) ?_ ?_ ?_
  · exact Derives.andR (A := 𝐆 p) (B := 𝐆 q) (by simp)
      (.ax (A := 𝐆 p) (by simp) (by simp))
      (.ax (A := 𝐆 q) (by simp) (by simp))
  · refine Derives.andL (A := 𝐆 p) (B := 𝐆 q) (by simp) ?_
    refine Derives.alwaysL (A := p) (by simp) ?_
    refine Derives.alwaysL (A := q) (by simp) ?_
    refine Derives.step (Γ' := [𝐆 p, 𝐆 q]) (B := (𝐆 p) ⋏ (𝐆 q)) ?_ (by simp) (by simp)
    exact Derives.andR (A := 𝐆 p) (B := 𝐆 q) (by simp)
      (.ax (A := 𝐆 p) (by simp) (by simp))
      (.ax (A := 𝐆 q) (by simp) (by simp))
  · refine Derives.andL (A := 𝐆 p) (B := 𝐆 q) (by simp) ?_
    refine Derives.alwaysL (A := p) (by simp) ?_
    refine Derives.alwaysL (A := q) (by simp) ?_
    exact Derives.andR (A := p) (B := q) (by simp)
      (.ax (A := p) (by simp) (by simp))
      (.ax (A := q) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐆 (q) ⇒ 𝐆 ((p ⋏ q)))] :=
  Candidate.candidate p q

#print axioms verified
