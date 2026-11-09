import LTL

open LTL

-- LTL law 50: ◇ ◇ p ≈ ◇ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐅 (𝐅 (p))] ⊢ [𝐅 (p)]) ∧ ([𝐅 (p)] ⊢ [𝐅 (𝐅 (p))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.evL (A := 𝐅 p) (𝐅 p) (by simp)
      (Derives.ax (A := 𝐅 p) (by simp) (by simp))
      (Derives.evR (A := p) (by simp)
        (Derives.ax (A := 𝐗 (𝐅 p)) (by simp) (by simp)))
      (Derives.ax (A := 𝐅 p) (by simp) (by simp))
  · exact Derives.evR (A := 𝐅 p) (by simp)
      (Derives.ax (A := 𝐅 p) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐅 (𝐅 (p))] ⊢ [𝐅 (p)]) ∧ ([𝐅 (p)] ⊢ [𝐅 (𝐅 (p))]) :=
  Candidate.candidate p

#print axioms verified
