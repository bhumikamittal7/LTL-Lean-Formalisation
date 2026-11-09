import LTL

open LTL

-- LTL law 38: ◇ p ≈ ⊤ U p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐅 (p)] ⊢ [(⊤ₗ 𝐔 p)]) ∧ ([(⊤ₗ 𝐔 p)] ⊢ [𝐅 (p)]) := by
  refine ⟨?_, ?_⟩
  · refine Derives.evL (A := p) (I := (⊤ₗ 𝐔 p)) (by simp) ?_ ?_ ?_
    · refine Derives.untilR (A := ⊤ₗ) (B := p) (by simp) ?_ ?_
      · exact Derives.ax (A := p) (by simp) (by simp)
      · exact Derives.ax (A := p) (by simp) (by simp)
    · refine Derives.untilR (A := ⊤ₗ) (B := p) (by simp) ?_ ?_
      · exact Derives.topR (by simp)
      · exact Derives.ax (A := 𝐗 (⊤ₗ 𝐔 p)) (by simp) (by simp)
    · exact Derives.ax (A := (⊤ₗ 𝐔 p)) (by simp) (by simp)
  · refine Derives.untilL (A := ⊤ₗ) (B := p) (I := 𝐅 p) (by simp) ?_ ?_ ?_
    · refine Derives.evR (A := p) (by simp) ?_
      exact Derives.ax (A := p) (by simp) (by simp)
    · refine Derives.evR (A := p) (by simp) ?_
      exact Derives.ax (A := 𝐗 (𝐅 p)) (by simp) (by simp)
    · exact Derives.ax (A := 𝐅 p) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐅 (p)] ⊢ [(⊤ₗ 𝐔 p)]) ∧ ([(⊤ₗ 𝐔 p)] ⊢ [𝐅 (p)]) :=
  Candidate.candidate p

#print axioms verified
