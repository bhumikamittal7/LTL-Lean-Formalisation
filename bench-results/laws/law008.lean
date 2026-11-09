import LTL

open LTL

-- LTL law 8: ◯ ⊥ ≈ ⊥
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} :
    ([𝐗 ((⊥ₗ : Formula AP))] ⊢ [(⊥ₗ : Formula AP)]) ∧ ([(⊥ₗ : Formula AP)] ⊢ [𝐗 ((⊥ₗ : Formula AP))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.next (Γ' := [(⊥ₗ : Formula AP)]) (Δ' := ([] : List (Formula AP)))
      (Derives.botL (by simp)) (by simp) (by simp)
  · exact Derives.botL (by simp)

end Candidate

theorem verified {AP : Type} :
    ([𝐗 ((⊥ₗ : Formula AP))] ⊢ [(⊥ₗ : Formula AP)]) ∧ ([(⊥ₗ : Formula AP)] ⊢ [𝐗 ((⊥ₗ : Formula AP))]) :=
  Candidate.candidate 

#print axioms verified
