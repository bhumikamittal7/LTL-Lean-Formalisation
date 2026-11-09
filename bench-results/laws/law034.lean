import LTL

open LTL

-- LTL law 34: (p U q) ∨ (p ∧ q) ≈ p U q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([((p 𝐔 q) ⋎ (p ⋏ q))] ⊢ [(p 𝐔 q)]) ∧ ([(p 𝐔 q)] ⊢ [((p 𝐔 q) ⋎ (p ⋏ q))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.orL (A := p 𝐔 q) (B := p ⋏ q) (by simp)
      (Derives.ax (A := p 𝐔 q) (by simp) (by simp))
      (Derives.andL (A := p) (B := q) (by simp)
        (Derives.untilR (A := p) (B := q) (by simp)
          (Derives.ax (A := q) (by simp) (by simp))
          (Derives.ax (A := q) (by simp) (by simp))))
  · exact Derives.orR (A := p 𝐔 q) (B := p ⋏ q) (by simp)
      (Derives.ax (A := p 𝐔 q) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([((p 𝐔 q) ⋎ (p ⋏ q))] ⊢ [(p 𝐔 q)]) ∧ ([(p 𝐔 q)] ⊢ [((p 𝐔 q) ⋎ (p ⋏ q))]) :=
  Candidate.candidate p q

#print axioms verified
