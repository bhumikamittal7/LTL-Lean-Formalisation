import LTL

open LTL

-- LTL law 69: □ p ∨ p ≈ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([(𝐆 (p) ⋎ p)] ⊢ [p]) ∧ ([p] ⊢ [(𝐆 (p) ⋎ p)]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.orL (A := 𝐆 p) (B := p) (by simp)
      (Derives.alwaysL (A := p) (by simp) (Derives.ax (A := p) (by simp) (by simp)))
      (Derives.ax (A := p) (by simp) (by simp))
  · exact Derives.orR (A := 𝐆 p) (B := p) (by simp)
      (Derives.ax (A := p) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(𝐆 (p) ⋎ p)] ⊢ [p]) ∧ ([p] ⊢ [(𝐆 (p) ⋎ p)]) :=
  Candidate.candidate p

#print axioms verified
