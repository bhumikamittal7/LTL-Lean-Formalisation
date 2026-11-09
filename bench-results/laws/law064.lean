import LTL

open LTL

-- LTL law 64: □ ⊤ ≈ ⊤
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} :
    ([𝐆 ((⊤ₗ : Formula AP))] ⊢ [(⊤ₗ : Formula AP)]) ∧ ([(⊤ₗ : Formula AP)] ⊢ [𝐆 ((⊤ₗ : Formula AP))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.topR (by simp)
  · exact Derives.alwaysR (A := (⊤ₗ : Formula AP)) (⊤ₗ : Formula AP) (by simp)
      (Derives.topR (by simp))
      (Derives.step (Γ' := ([] : List (Formula AP))) (B := (⊤ₗ : Formula AP))
        (Derives.topR (by simp)) (by simp) (by simp))
      (Derives.topR (by simp))

end Candidate

theorem verified {AP : Type} :
    ([𝐆 ((⊤ₗ : Formula AP))] ⊢ [(⊤ₗ : Formula AP)]) ∧ ([(⊤ₗ : Formula AP)] ⊢ [𝐆 ((⊤ₗ : Formula AP))]) :=
  Candidate.candidate 

#print axioms verified
