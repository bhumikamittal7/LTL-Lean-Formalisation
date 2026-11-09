import LTL

open LTL

-- LTL law 65: □ ⊥ ≈ ⊥
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} :
    ([𝐆 ((⊥ₗ : Formula AP))] ⊢ [(⊥ₗ : Formula AP)]) ∧ ([(⊥ₗ : Formula AP)] ⊢ [𝐆 ((⊥ₗ : Formula AP))]) :=
  ⟨.alwaysL (A := (⊥ₗ : Formula AP)) (by simp) (.botL (by simp)),
   .botL (by simp)⟩

end Candidate

theorem verified {AP : Type} :
    ([𝐆 ((⊥ₗ : Formula AP))] ⊢ [(⊥ₗ : Formula AP)]) ∧ ([(⊥ₗ : Formula AP)] ⊢ [𝐆 ((⊥ₗ : Formula AP))]) :=
  Candidate.candidate 

#print axioms verified
