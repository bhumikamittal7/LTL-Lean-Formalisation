import LTL

open LTL

-- LTL law 39: (p U q) ∧ ◇ q ≈ p U q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([((p 𝐔 q) ⋏ 𝐅 (q))] ⊢ [(p 𝐔 q)]) ∧ ([(p 𝐔 q)] ⊢ [((p 𝐔 q) ⋏ 𝐅 (q))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.andL (A := p 𝐔 q) (B := 𝐅 q) (by simp)
      (Derives.ax (A := p 𝐔 q) (by simp) (by simp))
  · refine Derives.andR (A := p 𝐔 q) (B := 𝐅 q) (by simp)
      (Derives.ax (A := p 𝐔 q) (by simp) (by simp)) ?_
    refine Derives.untilL (I := 𝐅 q) (A := p) (B := q) (by simp) ?_ ?_ ?_
    · exact Derives.evR (A := q) (by simp) (Derives.ax (A := q) (by simp) (by simp))
    · exact Derives.evR (A := q) (by simp)
        (Derives.ax (A := 𝐗 (𝐅 q)) (by simp) (by simp))
    · exact Derives.ax (A := 𝐅 q) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([((p 𝐔 q) ⋏ 𝐅 (q))] ⊢ [(p 𝐔 q)]) ∧ ([(p 𝐔 q)] ⊢ [((p 𝐔 q) ⋏ 𝐅 (q))]) :=
  Candidate.candidate p q

#print axioms verified
