import LTL

open LTL

-- LTL law 31: p ∨ (p U q) ≈ p ∨ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([(p ⋎ (p 𝐔 q))] ⊢ [(p ⋎ q)]) ∧ ([(p ⋎ q)] ⊢ [(p ⋎ (p 𝐔 q))]) := by
  constructor
  · refine Derives.orL (A := p) (B := p 𝐔 q) (by simp) ?_ ?_
    · exact Derives.orR (A := p) (B := q) (by simp) (.ax (A := p) (by simp) (by simp))
    · refine Derives.untilL (A := p) (B := q) (p ⋎ q) (by simp) ?_ ?_ ?_
      · exact Derives.orR (A := p) (B := q) (by simp) (.ax (A := q) (by simp) (by simp))
      · exact Derives.orR (A := p) (B := q) (by simp) (.ax (A := p) (by simp) (by simp))
      · exact .ax (A := p ⋎ q) (by simp) (by simp)
  · refine Derives.orR (A := p) (B := p 𝐔 q) (by simp) ?_
    refine Derives.orL (A := p) (B := q) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · refine Derives.untilR (A := p) (B := q) (by simp) ?_ ?_
      · exact .ax (A := q) (by simp) (by simp)
      · exact .ax (A := q) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([(p ⋎ (p 𝐔 q))] ⊢ [(p ⋎ q)]) ∧ ([(p ⋎ q)] ⊢ [(p ⋎ (p 𝐔 q))]) :=
  Candidate.candidate p q

#print axioms verified
