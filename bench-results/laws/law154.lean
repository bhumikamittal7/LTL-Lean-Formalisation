import LTL

open LTL

-- LTL law 154: ◇ □ ◇ □ p ≈ ◇ □ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐅 (𝐆 (𝐅 (𝐆 (p))))] ⊢ [𝐅 (𝐆 (p))]) ∧ ([𝐅 (𝐆 (p))] ⊢ [𝐅 (𝐆 (𝐅 (𝐆 (p))))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.evL (A := 𝐆 (𝐅 (𝐆 p))) (𝐅 (𝐆 p)) (by simp)
      (Derives.alwaysL (A := 𝐅 (𝐆 p)) (by simp)
        (Derives.ax (A := 𝐅 (𝐆 p)) (by simp) (by simp)))
      (Derives.evR (A := 𝐆 p) (by simp)
        (Derives.ax (A := 𝐗 (𝐅 (𝐆 p))) (by simp) (by simp)))
      (Derives.ax (A := 𝐅 (𝐆 p)) (by simp) (by simp))
  · exact Derives.evL (A := 𝐆 p) (𝐅 (𝐆 (𝐅 (𝐆 p)))) (by simp)
      (Derives.evR (A := 𝐆 (𝐅 (𝐆 p))) (by simp)
        (Derives.alwaysR (A := 𝐅 (𝐆 p)) (𝐆 p) (by simp)
          (Derives.ax (A := 𝐆 p) (by simp) (by simp))
          (Derives.alwaysL (A := p) (by simp)
            (Derives.ax (A := 𝐗 (𝐆 p)) (by simp) (by simp)))
          (Derives.evR (A := 𝐆 p) (by simp)
            (Derives.ax (A := 𝐆 p) (by simp) (by simp)))))
      (Derives.evR (A := 𝐆 (𝐅 (𝐆 p))) (by simp)
        (Derives.ax (A := 𝐗 (𝐅 (𝐆 (𝐅 (𝐆 p))))) (by simp) (by simp)))
      (Derives.ax (A := 𝐅 (𝐆 (𝐅 (𝐆 p)))) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐅 (𝐆 (𝐅 (𝐆 (p))))] ⊢ [𝐅 (𝐆 (p))]) ∧ ([𝐅 (𝐆 (p))] ⊢ [𝐅 (𝐆 (𝐅 (𝐆 (p))))]) :=
  Candidate.candidate p

#print axioms verified
