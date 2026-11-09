import LTL

open LTL

-- LTL law 97: □ ◇ p ∧ ◇ □ ¬p ≈ ⊥
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([(𝐆 (𝐅 (p)) ⋏ 𝐅 (𝐆 (∼(p))))] ⊢ [⊥ₗ]) ∧ ([⊥ₗ] ⊢ [(𝐆 (𝐅 (p)) ⋏ 𝐅 (𝐆 (∼(p))))]) := by
  refine ⟨?_, ?_⟩
  · refine Derives.andL (A := 𝐆 (𝐅 p)) (B := 𝐅 (𝐆 (∼p))) (by simp) ?_
    refine Derives.evL (A := 𝐆 (∼p)) (∼(𝐆 (𝐅 p))) (by simp) ?_ ?_ ?_
    · refine Derives.negR (A := 𝐆 (𝐅 p)) (by simp) ?_
      refine Derives.alwaysL (A := 𝐅 p) (by simp) ?_
      refine Derives.evL (A := p) (∼(𝐆 (∼p))) (by simp) ?_ ?_ ?_
      · refine Derives.negR (A := 𝐆 (∼p)) (by simp) ?_
        refine Derives.alwaysL (A := ∼p) (by simp) ?_
        refine Derives.negL (A := p) (by simp) ?_
        exact .ax (A := p) (by simp) (by simp)
      · refine Derives.negR (A := 𝐆 (∼p)) (by simp) ?_
        refine Derives.alwaysL (A := ∼p) (by simp) ?_
        refine Derives.next (Γ' := [𝐆 (∼p), ∼(𝐆 (∼p))]) (Δ' := []) ?_ ?_ ?_
        · refine Derives.negL (A := 𝐆 (∼p)) (by simp) ?_
          exact .ax (A := 𝐆 (∼p)) (by simp) (by simp)
        · simp
        · simp
      · refine Derives.negL (A := 𝐆 (∼p)) (by simp) ?_
        exact .ax (A := 𝐆 (∼p)) (by simp) (by simp)
    · refine Derives.negR (A := 𝐆 (𝐅 p)) (by simp) ?_
      refine Derives.alwaysL (A := 𝐅 p) (by simp) ?_
      refine Derives.next (Γ' := [𝐆 (𝐅 p), ∼(𝐆 (𝐅 p))]) (Δ' := []) ?_ ?_ ?_
      · refine Derives.negL (A := 𝐆 (𝐅 p)) (by simp) ?_
        exact .ax (A := 𝐆 (𝐅 p)) (by simp) (by simp)
      · simp
      · simp
    · refine Derives.negL (A := 𝐆 (𝐅 p)) (by simp) ?_
      exact .ax (A := 𝐆 (𝐅 p)) (by simp) (by simp)
  · exact Derives.botL (by simp)

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(𝐆 (𝐅 (p)) ⋏ 𝐅 (𝐆 (∼(p))))] ⊢ [⊥ₗ]) ∧ ([⊥ₗ] ⊢ [(𝐆 (𝐅 (p)) ⋏ 𝐅 (𝐆 (∼(p))))]) :=
  Candidate.candidate p

#print axioms verified
