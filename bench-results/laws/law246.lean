import LTL

open LTL

-- LTL law 246: (p U q) U r ⟹ (p ∨ q) U r
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r : Formula AP) :
    [((p 𝐔 q) 𝐔 r)] ⊢ [((p ⋎ q) 𝐔 r)] := by
  refine Derives.untilL (A := p 𝐔 q) (B := r) ((p ⋎ q) 𝐔 r) (by simp) ?_ ?_ ?_
  · exact Derives.untilR (A := p ⋎ q) (B := r) (by simp)
      (.ax (A := r) (by simp) (by simp)) (.ax (A := r) (by simp) (by simp))
  · refine Derives.untilR (A := p ⋎ q) (B := r) (by simp) ?_
      (.ax (A := 𝐗 ((p ⋎ q) 𝐔 r)) (by simp) (by simp))
    refine Derives.untilL (A := p) (B := q) (p ⋎ q) (by simp) ?_ ?_
      (.ax (A := p ⋎ q) (by simp) (by simp))
    · exact Derives.orR (A := p) (B := q) (by simp) (.ax (A := q) (by simp) (by simp))
    · exact Derives.orR (A := p) (B := q) (by simp) (.ax (A := p) (by simp) (by simp))
  · exact .ax (A := (p ⋎ q) 𝐔 r) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [((p 𝐔 q) 𝐔 r)] ⊢ [((p ⋎ q) 𝐔 r)] :=
  Candidate.candidate p q r

#print axioms verified
