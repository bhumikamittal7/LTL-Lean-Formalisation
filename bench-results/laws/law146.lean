import LTL

open LTL

-- LTL law 146: □ ◇ p ∨ □ ◇ ¬p ≈ ⊤
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([(𝐆 (𝐅 (p)) ⋎ 𝐆 (𝐅 (∼(p))))] ⊢ [⊤ₗ]) ∧ ([⊤ₗ] ⊢ [(𝐆 (𝐅 (p)) ⋎ 𝐆 (𝐅 (∼(p))))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.topR (by simp)
  · apply Derives.orR (A := 𝐆 (𝐅 p)) (B := 𝐆 (𝐅 (∼p))) (by simp)
    apply Derives.alwaysR (A := 𝐅 (∼p)) (∼(𝐆 (𝐅 p))) (by simp)
    · exact Derives.negR (A := 𝐆 (𝐅 p)) (by simp)
        (Derives.ax (A := 𝐆 (𝐅 p)) (by simp) (by simp))
    · apply Derives.negL (A := 𝐆 (𝐅 p)) (by simp)
      apply Derives.cut (𝐗 (𝐆 (𝐅 p)))
      · exact Derives.next (Γ' := []) (Δ' := [𝐆 (𝐅 p), ∼(𝐆 (𝐅 p))])
          (Derives.negR (A := 𝐆 (𝐅 p)) (by simp)
            (Derives.ax (A := 𝐆 (𝐅 p)) (by simp) (by simp))) (by simp) (by simp)
      · apply Derives.alwaysR (A := 𝐅 p) (𝐗 (𝐆 (𝐅 p))) (by simp)
        · exact Derives.ax (A := 𝐗 (𝐆 (𝐅 p))) (by simp) (by simp)
        · exact Derives.step (Γ' := [𝐆 (𝐅 p)]) (B := 𝐗 (𝐆 (𝐅 p)))
            (Derives.alwaysL (A := 𝐅 p) (by simp)
              (Derives.ax (A := 𝐗 (𝐆 (𝐅 p))) (by simp) (by simp))) (by simp) (by simp)
        · apply Derives.evR (A := p) (by simp)
          exact Derives.step (Γ' := [𝐆 (𝐅 p)]) (B := 𝐅 p)
            (Derives.alwaysL (A := 𝐅 p) (by simp)
              (Derives.ax (A := 𝐅 p) (by simp) (by simp))) (by simp) (by simp)
    · apply Derives.negL (A := 𝐆 (𝐅 p)) (by simp)
      apply Derives.alwaysR (A := 𝐅 p) (∼(𝐅 (∼p))) (by simp)
      · exact Derives.negR (A := 𝐅 (∼p)) (by simp)
          (Derives.ax (A := 𝐅 (∼p)) (by simp) (by simp))
      · apply Derives.negL (A := 𝐅 (∼p)) (by simp)
        apply Derives.cut (𝐗 (𝐅 (∼p)))
        · exact Derives.next (Γ' := []) (Δ' := [𝐅 (∼p), ∼(𝐅 (∼p))])
            (Derives.negR (A := 𝐅 (∼p)) (by simp)
              (Derives.ax (A := 𝐅 (∼p)) (by simp) (by simp))) (by simp) (by simp)
        · exact Derives.evR (A := ∼p) (by simp)
            (Derives.ax (A := 𝐗 (𝐅 (∼p))) (by simp) (by simp))
      · apply Derives.negL (A := 𝐅 (∼p)) (by simp)
        apply Derives.evR (A := ∼p) (by simp)
        apply Derives.negR (A := p) (by simp)
        apply Derives.evR (A := p) (by simp)
        exact Derives.ax (A := p) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(𝐆 (𝐅 (p)) ⋎ 𝐆 (𝐅 (∼(p))))] ⊢ [⊤ₗ]) ∧ ([⊤ₗ] ⊢ [(𝐆 (𝐅 (p)) ⋎ 𝐆 (𝐅 (∼(p))))]) :=
  Candidate.candidate p

#print axioms verified
