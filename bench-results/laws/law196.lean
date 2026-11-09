import LTL

open LTL

-- LTL law 196: p U q ≈ (p ∧ ¬q) U q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([(p 𝐔 q)] ⊢ [((p ⋏ ∼(q)) 𝐔 q)]) ∧ ([((p ⋏ ∼(q)) 𝐔 q)] ⊢ [(p 𝐔 q)]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.untilL (A := p) (B := q) (I := ((p ⋏ ∼(q)) 𝐔 q)) (by simp)
      (Derives.untilR (A := (p ⋏ ∼(q))) (B := q) (by simp)
        (Derives.ax (A := q) (by simp) (by simp))
        (Derives.ax (A := q) (by simp) (by simp)))
      (Derives.untilR (A := (p ⋏ ∼(q))) (B := q) (by simp)
        (Derives.andR (A := p) (B := ∼(q)) (by simp)
          (Derives.ax (A := p) (by simp) (by simp))
          (Derives.negR (A := q) (by simp)
            (Derives.ax (A := q) (by simp) (by simp))))
        (Derives.ax (A := 𝐗 ((p ⋏ ∼(q)) 𝐔 q)) (by simp) (by simp)))
      (Derives.ax (A := ((p ⋏ ∼(q)) 𝐔 q)) (by simp) (by simp))
  · exact Derives.untilL (A := (p ⋏ ∼(q))) (B := q) (I := (p 𝐔 q)) (by simp)
      (Derives.untilR (A := p) (B := q) (by simp)
        (Derives.ax (A := q) (by simp) (by simp))
        (Derives.ax (A := q) (by simp) (by simp)))
      (Derives.untilR (A := p) (B := q) (by simp)
        (Derives.andL (A := p) (B := ∼(q)) (by simp)
          (Derives.ax (A := p) (by simp) (by simp)))
        (Derives.ax (A := 𝐗 (p 𝐔 q)) (by simp) (by simp)))
      (Derives.ax (A := (p 𝐔 q)) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([(p 𝐔 q)] ⊢ [((p ⋏ ∼(q)) 𝐔 q)]) ∧ ([((p ⋏ ∼(q)) 𝐔 q)] ⊢ [(p 𝐔 q)]) :=
  Candidate.candidate p q

#print axioms verified
