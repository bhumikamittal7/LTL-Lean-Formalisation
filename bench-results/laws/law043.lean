import LTL

open LTL

-- LTL law 43: ◇ ⊤ ≈ ⊤
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} :
    ([𝐅 ((⊤ₗ : Formula AP))] ⊢ [(⊤ₗ : Formula AP)]) ∧ ([(⊤ₗ : Formula AP)] ⊢ [𝐅 ((⊤ₗ : Formula AP))]) :=
  ⟨Derives.topR (by simp),
   Derives.evR (A := (⊤ₗ : Formula AP)) (by simp)
     (Derives.ax (A := (⊤ₗ : Formula AP)) (by simp) (by simp))⟩

end Candidate

theorem verified {AP : Type} :
    ([𝐅 ((⊤ₗ : Formula AP))] ⊢ [(⊤ₗ : Formula AP)]) ∧ ([(⊤ₗ : Formula AP)] ⊢ [𝐅 ((⊤ₗ : Formula AP))]) :=
  Candidate.candidate 

#print axioms verified
