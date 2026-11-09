import LTL

open LTL

-- LTL law 71: □ p ∨ ◇ p ≈ ◇ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([(𝐆 (p) ⋎ 𝐅 (p))] ⊢ [𝐅 (p)]) ∧ ([𝐅 (p)] ⊢ [(𝐆 (p) ⋎ 𝐅 (p))]) := by
  refine ⟨?_, ?_⟩
  · refine Derives.orL (A := 𝐆 p) (B := 𝐅 p) (by simp) ?_ ?_
    · refine Derives.alwaysL (A := p) (by simp) ?_
      exact Derives.evR (A := p) (by simp) (Derives.ax (A := p) (by simp) (by simp))
    · exact Derives.ax (A := 𝐅 p) (by simp) (by simp)
  · exact Derives.orR (A := 𝐆 p) (B := 𝐅 p) (by simp)
      (Derives.ax (A := 𝐅 p) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(𝐆 (p) ⋎ 𝐅 (p))] ⊢ [𝐅 (p)]) ∧ ([𝐅 (p)] ⊢ [(𝐆 (p) ⋎ 𝐅 (p))]) :=
  Candidate.candidate p

#print axioms verified
