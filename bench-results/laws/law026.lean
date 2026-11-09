import LTL

open LTL

-- LTL law 26: (p U q) ∧ (¬q U p) ⟹ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [((p 𝐔 q) ⋏ (∼(q) 𝐔 p))] ⊢ [p] := by
  refine Derives.andL (A := p 𝐔 q) (B := ∼q 𝐔 p) (by simp) ?_
  refine Derives.untilL (A := p) (B := q) (I := q ⋎ p) (by simp) ?_ ?_ ?_
  · exact Derives.orR (A := q) (B := p) (by simp) (.ax (A := q) (by simp) (by simp))
  · exact Derives.orR (A := q) (B := p) (by simp) (.ax (A := p) (by simp) (by simp))
  refine Derives.untilL (A := ∼q) (B := p) (I := p ⋎ ∼q) (by simp) ?_ ?_ ?_
  · exact Derives.orR (A := p) (B := ∼q) (by simp) (.ax (A := p) (by simp) (by simp))
  · exact Derives.orR (A := p) (B := ∼q) (by simp) (.ax (A := ∼q) (by simp) (by simp))
  refine Derives.orL (A := p) (B := ∼q) (by simp) ?_ ?_
  · exact .ax (A := p) (by simp) (by simp)
  · refine Derives.orL (A := q) (B := p) (by simp) ?_ ?_
    · exact Derives.negL (A := q) (by simp) (.ax (A := q) (by simp) (by simp))
    · exact .ax (A := p) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [((p 𝐔 q) ⋏ (∼(q) 𝐔 p))] ⊢ [p] :=
  Candidate.candidate p q

#print axioms verified
