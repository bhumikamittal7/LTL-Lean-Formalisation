import LTL

open LTL

-- LTL law 27: p ∧ (¬p U q) ⟹ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [(p ⋏ (∼(p) 𝐔 q))] ⊢ [q] := by
  refine .andL (A := p) (B := ∼p 𝐔 q) (by simp) ?_
  refine .untilL (A := ∼p) (B := q) (q ⋎ ∼p) (by simp) ?_ ?_ ?_
  · exact .orR (A := q) (B := ∼p) (by simp) (.ax (A := q) (by simp) (by simp))
  · exact .orR (A := q) (B := ∼p) (by simp) (.ax (A := ∼p) (by simp) (by simp))
  · exact .orL (A := q) (B := ∼p) (by simp)
        (.ax (A := q) (by simp) (by simp))
        (.negL (A := p) (by simp) (.ax (A := p) (by simp) (by simp)))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [(p ⋏ (∼(p) 𝐔 q))] ⊢ [q] :=
  Candidate.candidate p q

#print axioms verified
