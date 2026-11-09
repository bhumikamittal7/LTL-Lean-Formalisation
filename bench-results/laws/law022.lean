import LTL

open LTL

-- LTL law 22: p U p ≈ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([(p 𝐔 p)] ⊢ [p]) ∧ ([p] ⊢ [(p 𝐔 p)]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.untilL (A := p) (B := p) (I := p) (by simp)
      (Derives.ax (A := p) (by simp) (by simp))
      (Derives.ax (A := p) (by simp) (by simp))
      (Derives.ax (A := p) (by simp) (by simp))
  · exact Derives.untilR (A := p) (B := p) (by simp)
      (Derives.ax (A := p) (by simp) (by simp))
      (Derives.ax (A := p) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(p 𝐔 p)] ⊢ [p]) ∧ ([p] ⊢ [(p 𝐔 p)]) :=
  Candidate.candidate p

#print axioms verified
