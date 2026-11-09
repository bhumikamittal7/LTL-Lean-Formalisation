import LTL

open LTL

-- LTL law 36: p U (p U q) ≈ p U q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([(p 𝐔 (p 𝐔 q))] ⊢ [(p 𝐔 q)]) ∧ ([(p 𝐔 q)] ⊢ [(p 𝐔 (p 𝐔 q))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.untilL (A := p) (B := p 𝐔 q) (I := p 𝐔 q) (by simp)
      (Derives.ax (A := p 𝐔 q) (by simp) (by simp))
      (Derives.untilR (A := p) (B := q) (by simp)
        (Derives.ax (A := p) (by simp) (by simp))
        (Derives.ax (A := 𝐗 (p 𝐔 q)) (by simp) (by simp)))
      (Derives.ax (A := p 𝐔 q) (by simp) (by simp))
  · exact Derives.untilR (A := p) (B := p 𝐔 q) (by simp)
      (Derives.ax (A := p 𝐔 q) (by simp) (by simp))
      (Derives.ax (A := p 𝐔 q) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([(p 𝐔 (p 𝐔 q))] ⊢ [(p 𝐔 q)]) ∧ ([(p 𝐔 q)] ⊢ [(p 𝐔 (p 𝐔 q))]) :=
  Candidate.candidate p q

#print axioms verified
