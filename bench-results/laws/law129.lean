import LTL

open LTL

-- LTL law 129: □ (p ⇒ q ∧ ◯ p) ⟹ (p ⇒ □ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ (q ⋏ 𝐗 (p))))] ⊢ [(p ⇒ 𝐆 (q))] := by
  refine Derives.impR (A := p) (B := 𝐆 q) (by simp) ?_
  refine Derives.alwaysR (I := p ⋏ 𝐆 (p ⇒ (q ⋏ 𝐗 p))) (A := q) (by simp) ?_ ?_ ?_
  · refine Derives.andR (A := p) (B := 𝐆 (p ⇒ (q ⋏ 𝐗 p))) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · exact .ax (A := 𝐆 (p ⇒ (q ⋏ 𝐗 p))) (by simp) (by simp)
  · refine Derives.andL (A := p) (B := 𝐆 (p ⇒ (q ⋏ 𝐗 p))) (by simp) ?_
    refine Derives.alwaysL (A := (p ⇒ (q ⋏ 𝐗 p))) (by simp) ?_
    refine Derives.impL (A := p) (B := q ⋏ 𝐗 p) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · refine Derives.andL (A := q) (B := 𝐗 p) (by simp) ?_
      refine Derives.step (Γ' := [p, 𝐆 (p ⇒ (q ⋏ 𝐗 p))])
        (B := p ⋏ 𝐆 (p ⇒ (q ⋏ 𝐗 p))) ?_ (by simp) (by simp)
      refine Derives.andR (A := p) (B := 𝐆 (p ⇒ (q ⋏ 𝐗 p))) (by simp) ?_ ?_
      · exact .ax (A := p) (by simp) (by simp)
      · exact .ax (A := 𝐆 (p ⇒ (q ⋏ 𝐗 p))) (by simp) (by simp)
  · refine Derives.andL (A := p) (B := 𝐆 (p ⇒ (q ⋏ 𝐗 p))) (by simp) ?_
    refine Derives.alwaysL (A := (p ⇒ (q ⋏ 𝐗 p))) (by simp) ?_
    refine Derives.impL (A := p) (B := q ⋏ 𝐗 p) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · refine Derives.andL (A := q) (B := 𝐗 p) (by simp) ?_
      exact .ax (A := q) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ (q ⋏ 𝐗 (p))))] ⊢ [(p ⇒ 𝐆 (q))] :=
  Candidate.candidate p q

#print axioms verified
