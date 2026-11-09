import LTL

open LTL

-- LTL law 149: □ p ⟹ (◇ q ⇒ ◇ (p U q))
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐅 (q) ⇒ 𝐅 ((p 𝐔 q)))] := by
  refine Derives.impR (A := 𝐅 q) (B := 𝐅 (p 𝐔 q)) (by simp) ?_
  refine Derives.evL (A := q) ((𝐆 p) ⇒ (p 𝐔 q)) (by simp) ?_ ?_ ?_
  · refine Derives.impR (A := 𝐆 p) (B := p 𝐔 q) (by simp) ?_
    refine Derives.untilR (A := p) (B := q) (by simp) ?_ ?_
    · exact .ax (A := q) (by simp) (by simp)
    · exact .ax (A := q) (by simp) (by simp)
  · refine Derives.impR (A := 𝐆 p) (B := p 𝐔 q) (by simp) ?_
    refine Derives.alwaysL (A := p) (by simp) ?_
    refine Derives.untilR (A := p) (B := q) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · refine Derives.step (Γ' := [𝐆 p, (𝐆 p) ⇒ (p 𝐔 q)]) (B := p 𝐔 q) ?_ (by simp) (by simp)
      refine Derives.impL (A := 𝐆 p) (B := p 𝐔 q) (by simp) ?_ ?_
      · exact .ax (A := 𝐆 p) (by simp) (by simp)
      · exact .ax (A := p 𝐔 q) (by simp) (by simp)
  · refine Derives.impL (A := 𝐆 p) (B := p 𝐔 q) (by simp) ?_ ?_
    · exact .ax (A := 𝐆 p) (by simp) (by simp)
    · refine Derives.evR (A := p 𝐔 q) (by simp) ?_
      exact .ax (A := p 𝐔 q) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐅 (q) ⇒ 𝐅 ((p 𝐔 q)))] :=
  Candidate.candidate p q

#print axioms verified
