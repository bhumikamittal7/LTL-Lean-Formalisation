import LTL

open LTL

-- LTL law 143: (p ∧ q) U r ⟹ (p U q) U r
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r : Formula AP) :
    [((p ⋏ q) 𝐔 r)] ⊢ [((p 𝐔 q) 𝐔 r)] := by
  refine .untilL (A := p ⋏ q) (B := r) ((p 𝐔 q) 𝐔 r) (by simp) ?_ ?_ ?_
  · exact .untilR (A := p 𝐔 q) (B := r) (by simp)
      (.ax (A := r) (by simp) (by simp))
      (.ax (A := r) (by simp) (by simp))
  · refine .untilR (A := p 𝐔 q) (B := r) (by simp) ?_
      (.ax (A := 𝐗 ((p 𝐔 q) 𝐔 r)) (by simp) (by simp))
    refine .andL (A := p) (B := q) (by simp) ?_
    exact .untilR (A := p) (B := q) (by simp)
      (.ax (A := q) (by simp) (by simp))
      (.ax (A := q) (by simp) (by simp))
  · exact .ax (A := (p 𝐔 q) 𝐔 r) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [((p ⋏ q) 𝐔 r)] ⊢ [((p 𝐔 q) 𝐔 r)] :=
  Candidate.candidate p q r

#print axioms verified
