import LTL

open LTL

-- LTL law 20: p U ⊤ ≈ ⊤
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([(p 𝐔 ⊤ₗ)] ⊢ [⊤ₗ]) ∧ ([⊤ₗ] ⊢ [(p 𝐔 ⊤ₗ)]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.topR (by simp)
  · exact Derives.untilR (A := p) (B := ⊤ₗ) (by simp)
      (Derives.topR (by simp))
      (Derives.topR (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(p 𝐔 ⊤ₗ)] ⊢ [⊤ₗ]) ∧ ([⊤ₗ] ⊢ [(p 𝐔 ⊤ₗ)]) :=
  Candidate.candidate p

#print axioms verified
