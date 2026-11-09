import LTL

open LTL

-- LTL law 132: □ (□ p ⇒ q) ⟹ (□ p ⇒ □ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 ((𝐆 (p) ⇒ q))] ⊢ [(𝐆 (p) ⇒ 𝐆 (q))] := by
  refine Derives.impR (A := 𝐆 p) (B := 𝐆 q) (by simp) ?_
  refine Derives.alwaysR (A := q) (𝐆 p ⋏ 𝐆 (𝐆 p ⇒ q)) (by simp) ?_ ?_ ?_
  · refine Derives.andR (A := 𝐆 p) (B := 𝐆 (𝐆 p ⇒ q)) (by simp) ?_ ?_
    · exact .ax (A := 𝐆 p) (by simp) (by simp)
    · exact .ax (A := 𝐆 (𝐆 p ⇒ q)) (by simp) (by simp)
  · refine Derives.andL (A := 𝐆 p) (B := 𝐆 (𝐆 p ⇒ q)) (by simp) ?_
    refine Derives.alwaysL (A := p) (by simp) ?_
    refine Derives.alwaysL (A := 𝐆 p ⇒ q) (by simp) ?_
    refine Derives.step (Γ' := [𝐆 p, 𝐆 (𝐆 p ⇒ q)]) (B := 𝐆 p ⋏ 𝐆 (𝐆 p ⇒ q)) ?_ (by simp) (by simp)
    refine Derives.andR (A := 𝐆 p) (B := 𝐆 (𝐆 p ⇒ q)) (by simp) ?_ ?_
    · exact .ax (A := 𝐆 p) (by simp) (by simp)
    · exact .ax (A := 𝐆 (𝐆 p ⇒ q)) (by simp) (by simp)
  · refine Derives.andL (A := 𝐆 p) (B := 𝐆 (𝐆 p ⇒ q)) (by simp) ?_
    refine Derives.alwaysL (A := 𝐆 p ⇒ q) (by simp) ?_
    refine Derives.impL (A := 𝐆 p) (B := q) (by simp) ?_ ?_
    · exact .ax (A := 𝐆 p) (by simp) (by simp)
    · exact .ax (A := q) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 ((𝐆 (p) ⇒ q))] ⊢ [(𝐆 (p) ⇒ 𝐆 (q))] :=
  Candidate.candidate p q

#print axioms verified
