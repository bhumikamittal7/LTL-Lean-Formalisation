import LTL

open LTL

-- LTL law 96: ◇ □ p ∨ □ ◇ ¬p ≈ ⊤
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([(𝐅 (𝐆 (p)) ⋎ 𝐆 (𝐅 (∼(p))))] ⊢ [⊤ₗ]) ∧ ([⊤ₗ] ⊢ [(𝐅 (𝐆 (p)) ⋎ 𝐆 (𝐅 (∼(p))))]) := by
  refine ⟨Derives.topR (by simp), ?_⟩
  refine Derives.orR (A := 𝐅 (𝐆 p)) (B := 𝐆 (𝐅 (∼p))) (by simp) ?_
  refine Derives.alwaysR (A := 𝐅 (∼p)) (∼(𝐅 (𝐆 p))) (by simp) ?_ ?_ ?_
  · exact Derives.negR (A := 𝐅 (𝐆 p)) (by simp)
      (Derives.ax (A := 𝐅 (𝐆 p)) (by simp) (by simp))
  · refine Derives.negL (A := 𝐅 (𝐆 p)) (by simp) ?_
    refine Derives.evR (A := 𝐆 p) (by simp) ?_
    refine Derives.next (Γ' := []) (Δ' := [𝐅 (𝐆 p), ∼(𝐅 (𝐆 p))]) ?_ (by simp) (by simp)
    exact Derives.negR (A := 𝐅 (𝐆 p)) (by simp)
      (Derives.ax (A := 𝐅 (𝐆 p)) (by simp) (by simp))
  · refine Derives.negL (A := 𝐅 (𝐆 p)) (by simp) ?_
    refine Derives.evR (A := 𝐆 p) (by simp) ?_
    refine Derives.alwaysR (A := p) (∼(𝐅 (∼p))) (by simp) ?_ ?_ ?_
    · exact Derives.negR (A := 𝐅 (∼p)) (by simp)
        (Derives.ax (A := 𝐅 (∼p)) (by simp) (by simp))
    · refine Derives.negL (A := 𝐅 (∼p)) (by simp) ?_
      refine Derives.evR (A := ∼p) (by simp) ?_
      refine Derives.next (Γ' := []) (Δ' := [𝐅 (∼p), ∼(𝐅 (∼p))]) ?_ (by simp) (by simp)
      exact Derives.negR (A := 𝐅 (∼p)) (by simp)
        (Derives.ax (A := 𝐅 (∼p)) (by simp) (by simp))
    · refine Derives.negL (A := 𝐅 (∼p)) (by simp) ?_
      refine Derives.evR (A := ∼p) (by simp) ?_
      exact Derives.negR (A := p) (by simp)
        (Derives.ax (A := p) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(𝐅 (𝐆 (p)) ⋎ 𝐆 (𝐅 (∼(p))))] ⊢ [⊤ₗ]) ∧ ([⊤ₗ] ⊢ [(𝐅 (𝐆 (p)) ⋎ 𝐆 (𝐅 (∼(p))))]) :=
  Candidate.candidate p

#print axioms verified
