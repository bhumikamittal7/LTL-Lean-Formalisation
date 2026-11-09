import LTL

open LTL

-- LTL law 44: ◇ ⊥ ≈ ⊥
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} :
    ([𝐅 ((⊥ₗ : Formula AP))] ⊢ [(⊥ₗ : Formula AP)]) ∧ ([(⊥ₗ : Formula AP)] ⊢ [𝐅 ((⊥ₗ : Formula AP))]) :=
  ⟨Derives.evL (A := (⊥ₗ : Formula AP)) (I := (⊥ₗ : Formula AP)) (by simp)
     (Derives.botL (by simp))
     (Derives.next (Γ' := [(⊥ₗ : Formula AP)]) (Δ' := ([] : List (Formula AP)))
        (Derives.botL (by simp)) (by simp) (by simp))
     (Derives.botL (by simp)),
   Derives.botL (by simp)⟩

end Candidate

theorem verified {AP : Type} :
    ([𝐅 ((⊥ₗ : Formula AP))] ⊢ [(⊥ₗ : Formula AP)]) ∧ ([(⊥ₗ : Formula AP)] ⊢ [𝐅 ((⊥ₗ : Formula AP))]) :=
  Candidate.candidate 

#print axioms verified
