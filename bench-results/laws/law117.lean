import LTL

open LTL

-- LTL law 117: □ p ⟹ (□ q ⇒ □ (p ≡ q))
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐆 (q) ⇒ 𝐆 (((p ⇒ q) ⋏ (q ⇒ p))))] := by
  refine Derives.impR (A := 𝐆 q) (B := 𝐆 ((p ⇒ q) ⋏ (q ⇒ p))) (by simp) ?_
  refine Derives.alwaysR (I := 𝐆 p ⋏ 𝐆 q) (A := (p ⇒ q) ⋏ (q ⇒ p)) (by simp) ?_ ?_ ?_
  · refine Derives.andR (A := 𝐆 p) (B := 𝐆 q) (by simp) ?_ ?_
    · exact .ax (A := 𝐆 p) (by simp) (by simp)
    · exact .ax (A := 𝐆 q) (by simp) (by simp)
  · refine Derives.andL (A := 𝐆 p) (B := 𝐆 q) (by simp) ?_
    refine Derives.alwaysL (A := p) (by simp) ?_
    refine Derives.alwaysL (A := q) (by simp) ?_
    refine Derives.step (Γ' := [𝐆 p, 𝐆 q]) (B := 𝐆 p ⋏ 𝐆 q) ?_ (by simp) (by simp)
    refine Derives.andR (A := 𝐆 p) (B := 𝐆 q) (by simp) ?_ ?_
    · exact .ax (A := 𝐆 p) (by simp) (by simp)
    · exact .ax (A := 𝐆 q) (by simp) (by simp)
  · refine Derives.andL (A := 𝐆 p) (B := 𝐆 q) (by simp) ?_
    refine Derives.alwaysL (A := p) (by simp) ?_
    refine Derives.alwaysL (A := q) (by simp) ?_
    refine Derives.andR (A := p ⇒ q) (B := q ⇒ p) (by simp) ?_ ?_
    · refine Derives.impR (A := p) (B := q) (by simp) ?_
      exact .ax (A := q) (by simp) (by simp)
    · refine Derives.impR (A := q) (B := p) (by simp) ?_
      exact .ax (A := p) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐆 (q) ⇒ 𝐆 (((p ⇒ q) ⋏ (q ⇒ p))))] :=
  Candidate.candidate p q

#print axioms verified
