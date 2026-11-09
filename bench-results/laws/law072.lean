import LTL

open LTL

-- LTL law 72: □ □ p ≈ □ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐆 (𝐆 (p))] ⊢ [𝐆 (p)]) ∧ ([𝐆 (p)] ⊢ [𝐆 (𝐆 (p))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.alwaysL (A := 𝐆 p) (by simp)
      (Derives.ax (A := 𝐆 p) (by simp) (by simp))
  · exact Derives.alwaysR (I := 𝐆 p) (A := 𝐆 p) (by simp)
      (Derives.ax (A := 𝐆 p) (by simp) (by simp))
      (Derives.alwaysL (A := p) (by simp)
        (Derives.ax (A := 𝐗 (𝐆 p)) (by simp) (by simp)))
      (Derives.ax (A := 𝐆 p) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐆 (𝐆 (p))] ⊢ [𝐆 (p)]) ∧ ([𝐆 (p)] ⊢ [𝐆 (𝐆 (p))]) :=
  Candidate.candidate p

#print axioms verified
