import LTL

open LTL

-- LTL law 125: □ ((p ⇒ □ q) ∧ (q ⇒ □ r)) ⟹ (p ⇒ □ r)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r : Formula AP) :
    [𝐆 (((p ⇒ 𝐆 (q)) ⋏ (q ⇒ 𝐆 (r))))] ⊢ [(p ⇒ 𝐆 (r))] := by
  refine Derives.impR (A := p) (B := 𝐆 r) (by simp) ?_
  refine Derives.alwaysL (A := (p ⇒ 𝐆 q) ⋏ (q ⇒ 𝐆 r)) (by simp) ?_
  refine Derives.andL (A := p ⇒ 𝐆 q) (B := q ⇒ 𝐆 r) (by simp) ?_
  refine Derives.impL (A := p) (B := 𝐆 q) (by simp) ?_ ?_
  · exact Derives.ax (A := p) (by simp) (by simp)
  · refine Derives.alwaysL (A := q) (by simp) ?_
    refine Derives.impL (A := q) (B := 𝐆 r) (by simp) ?_ ?_
    · exact Derives.ax (A := q) (by simp) (by simp)
    · exact Derives.ax (A := 𝐆 r) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [𝐆 (((p ⇒ 𝐆 (q)) ⋏ (q ⇒ 𝐆 (r))))] ⊢ [(p ⇒ 𝐆 (r))] :=
  Candidate.candidate p q r

#print axioms verified
