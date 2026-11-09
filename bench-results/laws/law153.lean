import LTL

open LTL

-- LTL law 153: □ ◇ □ ◇ p ≈ □ ◇ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐆 (𝐅 (𝐆 (𝐅 (p))))] ⊢ [𝐆 (𝐅 (p))]) ∧ ([𝐆 (𝐅 (p))] ⊢ [𝐆 (𝐅 (𝐆 (𝐅 (p))))]) := by
  refine ⟨?_, ?_⟩
  · refine Derives.alwaysR (A := 𝐅 p) (I := 𝐆 (𝐅 (𝐆 (𝐅 p)))) (by simp) ?_ ?_ ?_
    · exact .ax (A := 𝐆 (𝐅 (𝐆 (𝐅 p)))) (by simp) (by simp)
    · exact .alwaysL (A := 𝐅 (𝐆 (𝐅 p))) (by simp)
        (.ax (A := 𝐗 (𝐆 (𝐅 (𝐆 (𝐅 p))))) (by simp) (by simp))
    · refine .alwaysL (A := 𝐅 (𝐆 (𝐅 p))) (by simp) ?_
      refine Derives.evL (A := 𝐆 (𝐅 p)) (I := 𝐅 p) (by simp) ?_ ?_ ?_
      · exact .alwaysL (A := 𝐅 p) (by simp) (.ax (A := 𝐅 p) (by simp) (by simp))
      · exact Derives.evR (A := p) (by simp) (.ax (A := 𝐗 (𝐅 p)) (by simp) (by simp))
      · exact .ax (A := 𝐅 p) (by simp) (by simp)
  · refine Derives.alwaysR (A := 𝐅 (𝐆 (𝐅 p))) (I := 𝐆 (𝐅 p)) (by simp) ?_ ?_ ?_
    · exact .ax (A := 𝐆 (𝐅 p)) (by simp) (by simp)
    · exact .alwaysL (A := 𝐅 p) (by simp) (.ax (A := 𝐗 (𝐆 (𝐅 p))) (by simp) (by simp))
    · exact Derives.evR (A := 𝐆 (𝐅 p)) (by simp) (.ax (A := 𝐆 (𝐅 p)) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐆 (𝐅 (𝐆 (𝐅 (p))))] ⊢ [𝐆 (𝐅 (p))]) ∧ ([𝐆 (𝐅 (p))] ⊢ [𝐆 (𝐅 (𝐆 (𝐅 (p))))]) :=
  Candidate.candidate p

#print axioms verified
