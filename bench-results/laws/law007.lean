import LTL

open LTL

-- LTL law 7: ◯ ⊤ ≈ ⊤
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} :
    ([𝐗 ((⊤ₗ : Formula AP))] ⊢ [(⊤ₗ : Formula AP)]) ∧ ([(⊤ₗ : Formula AP)] ⊢ [𝐗 ((⊤ₗ : Formula AP))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.topR (by simp)
  · exact Derives.step (Γ' := []) (B := (⊤ₗ : Formula AP))
      (Derives.topR (by simp)) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} :
    ([𝐗 ((⊤ₗ : Formula AP))] ⊢ [(⊤ₗ : Formula AP)]) ∧ ([(⊤ₗ : Formula AP)] ⊢ [𝐗 ((⊤ₗ : Formula AP))]) :=
  Candidate.candidate 

#print axioms verified
