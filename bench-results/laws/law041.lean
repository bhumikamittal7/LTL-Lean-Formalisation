import LTL

open LTL

-- LTL law 41: p U ◇ q ≈ ◇ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([(p 𝐔 𝐅 (q))] ⊢ [𝐅 (q)]) ∧ ([𝐅 (q)] ⊢ [(p 𝐔 𝐅 (q))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.untilL (A := p) (B := 𝐅 (q)) (I := 𝐅 (q)) (by simp)
      (Derives.ax (A := 𝐅 (q)) (by simp) (by simp))
      (Derives.evR (A := q) (by simp)
        (Derives.ax (A := 𝐗 (𝐅 (q))) (by simp) (by simp)))
      (Derives.ax (A := 𝐅 (q)) (by simp) (by simp))
  · exact Derives.untilR (A := p) (B := 𝐅 (q)) (by simp)
      (Derives.ax (A := 𝐅 (q)) (by simp) (by simp))
      (Derives.ax (A := 𝐅 (q)) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([(p 𝐔 𝐅 (q))] ⊢ [𝐅 (q)]) ∧ ([𝐅 (q)] ⊢ [(p 𝐔 𝐅 (q))]) :=
  Candidate.candidate p q

#print axioms verified
