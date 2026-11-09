import LTL

open LTL

-- LTL law 24: (¬p U (q U r)) ∧ (p U r) ⟹ q U r
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r : Formula AP) :
    [((∼(p) 𝐔 (q 𝐔 r)) ⋏ (p 𝐔 r))] ⊢ [(q 𝐔 r)] := by
  refine .andL (A := ∼p 𝐔 (q 𝐔 r)) (B := p 𝐔 r) (by simp) ?_
  refine .untilL (A := ∼p) (B := q 𝐔 r) ((q 𝐔 r) ⋎ ∼p) (by simp) ?_ ?_ ?_
  · exact .orR (A := q 𝐔 r) (B := ∼p) (by simp) (.ax (A := q 𝐔 r) (by simp) (by simp))
  · exact .orR (A := q 𝐔 r) (B := ∼p) (by simp) (.ax (A := ∼p) (by simp) (by simp))
  · refine .untilL (A := p) (B := r) (r ⋎ p) (by simp) ?_ ?_ ?_
    · exact .orR (A := r) (B := p) (by simp) (.ax (A := r) (by simp) (by simp))
    · exact .orR (A := r) (B := p) (by simp) (.ax (A := p) (by simp) (by simp))
    · refine .orL (A := q 𝐔 r) (B := ∼p) (by simp) ?_ ?_
      · exact .ax (A := q 𝐔 r) (by simp) (by simp)
      · refine .orL (A := r) (B := p) (by simp) ?_ ?_
        · exact .untilR (A := q) (B := r) (by simp)
            (.ax (A := r) (by simp) (by simp)) (.ax (A := r) (by simp) (by simp))
        · exact .negL (A := p) (by simp) (.ax (A := p) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [((∼(p) 𝐔 (q 𝐔 r)) ⋏ (p 𝐔 r))] ⊢ [(q 𝐔 r)] :=
  Candidate.candidate p q r

#print axioms verified
