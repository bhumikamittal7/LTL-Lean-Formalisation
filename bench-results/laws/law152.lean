import LTL

open LTL

-- LTL law 152: □ ◇ □ p ≈ ◇ □ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐆 (𝐅 (𝐆 (p)))] ⊢ [𝐅 (𝐆 (p))]) ∧ ([𝐅 (𝐆 (p))] ⊢ [𝐆 (𝐅 (𝐆 (p)))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.alwaysL (A := 𝐅 (𝐆 p)) (by simp)
      (Derives.ax (A := 𝐅 (𝐆 p)) (by simp) (by simp))
  · refine Derives.alwaysR (𝐅 (𝐆 p)) (A := 𝐅 (𝐆 p)) (by simp)
      (Derives.ax (A := 𝐅 (𝐆 p)) (by simp) (by simp)) ?_
      (Derives.ax (A := 𝐅 (𝐆 p)) (by simp) (by simp))
    refine Derives.evL (𝐗 (𝐅 (𝐆 p))) (A := 𝐆 p) (by simp) ?_ ?_
      (Derives.ax (A := 𝐗 (𝐅 (𝐆 p))) (by simp) (by simp))
    · exact Derives.alwaysL (A := p) (by simp)
        (Derives.step (Γ' := [𝐆 p]) (B := 𝐅 (𝐆 p))
          (Derives.evR (A := 𝐆 p) (by simp)
            (Derives.ax (A := 𝐆 p) (by simp) (by simp)))
          (by simp) (by simp))
    · exact Derives.step (Γ' := [𝐗 (𝐅 (𝐆 p))]) (B := 𝐅 (𝐆 p))
        (Derives.evR (A := 𝐆 p) (by simp)
          (Derives.ax (A := 𝐗 (𝐅 (𝐆 p))) (by simp) (by simp)))
        (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐆 (𝐅 (𝐆 (p)))] ⊢ [𝐅 (𝐆 (p))]) ∧ ([𝐅 (𝐆 (p))] ⊢ [𝐆 (𝐅 (𝐆 (p)))]) :=
  Candidate.candidate p

#print axioms verified
