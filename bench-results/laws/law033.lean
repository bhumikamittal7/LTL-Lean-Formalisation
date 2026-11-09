import LTL

open LTL

-- LTL law 33: (p U q) ∧ q ≈ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([((p 𝐔 q) ⋏ q)] ⊢ [q]) ∧ ([q] ⊢ [((p 𝐔 q) ⋏ q)]) := by
  refine ⟨?_, ?_⟩
  · exact .andL (A := p 𝐔 q) (B := q) (by simp)
      (.ax (A := q) (by simp) (by simp))
  · exact .andR (A := p 𝐔 q) (B := q) (by simp)
      (.untilR (A := p) (B := q) (by simp)
        (.ax (A := q) (by simp) (by simp))
        (.ax (A := q) (by simp) (by simp)))
      (.ax (A := q) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([((p 𝐔 q) ⋏ q)] ⊢ [q]) ∧ ([q] ⊢ [((p 𝐔 q) ⋏ q)]) :=
  Candidate.candidate p q

#print axioms verified
