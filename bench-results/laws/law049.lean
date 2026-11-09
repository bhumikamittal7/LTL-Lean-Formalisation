import LTL

open LTL

-- LTL law 49: ◇ p ∧ p ≈ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([(𝐅 (p) ⋏ p)] ⊢ [p]) ∧ ([p] ⊢ [(𝐅 (p) ⋏ p)]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.andL (A := 𝐅 p) (B := p) (by simp)
      (Derives.ax (A := p) (by simp) (by simp))
  · exact Derives.andR (A := 𝐅 p) (B := p) (by simp)
      (Derives.evR (A := p) (by simp)
        (Derives.ax (A := p) (by simp) (by simp)))
      (Derives.ax (A := p) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(𝐅 (p) ⋏ p)] ⊢ [p]) ∧ ([p] ⊢ [(𝐅 (p) ⋏ p)]) :=
  Candidate.candidate p

#print axioms verified
