import LTL

open LTL

-- LTL law 142: p U (q ∧ r) ⟹ p U (q U r)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r : Formula AP) :
    [(p 𝐔 (q ⋏ r))] ⊢ [(p 𝐔 (q 𝐔 r))] := by
  refine .untilL (A := p) (B := q ⋏ r) (I := p 𝐔 (q 𝐔 r)) (by simp) ?_ ?_ ?_
  · refine .andL (A := q) (B := r) (by simp) ?_
    refine .untilR (A := p) (B := q 𝐔 r) (by simp) ?_ ?_
    · exact .untilR (A := q) (B := r) (by simp)
        (.ax (A := r) (by simp) (by simp)) (.ax (A := r) (by simp) (by simp))
    · exact .untilR (A := q) (B := r) (by simp)
        (.ax (A := r) (by simp) (by simp)) (.ax (A := r) (by simp) (by simp))
  · refine .untilR (A := p) (B := q 𝐔 r) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · exact .ax (A := 𝐗 (p 𝐔 (q 𝐔 r))) (by simp) (by simp)
  · exact .ax (A := p 𝐔 (q 𝐔 r)) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [(p 𝐔 (q ⋏ r))] ⊢ [(p 𝐔 (q 𝐔 r))] :=
  Candidate.candidate p q r

#print axioms verified
