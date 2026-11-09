import LTL

open LTL

-- LTL law 192: ¬q U q ≈ ◇ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (q : Formula AP) :
    ([(∼(q) 𝐔 q)] ⊢ [𝐅 (q)]) ∧ ([𝐅 (q)] ⊢ [(∼(q) 𝐔 q)]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.untilL (A := ∼(q)) (B := q) (I := 𝐅 (q)) (by simp)
      (Derives.evR (A := q) (by simp) (.ax (A := q) (by simp) (by simp)))
      (Derives.evR (A := q) (by simp) (.ax (A := 𝐗 (𝐅 (q))) (by simp) (by simp)))
      (.ax (A := 𝐅 (q)) (by simp) (by simp))
  · exact Derives.evL (A := q) (I := (∼(q) 𝐔 q)) (by simp)
      (Derives.untilR (A := ∼(q)) (B := q) (by simp)
        (.ax (A := q) (by simp) (by simp))
        (.ax (A := q) (by simp) (by simp)))
      (Derives.untilR (A := ∼(q)) (B := q) (by simp)
        (Derives.negR (A := q) (by simp) (.ax (A := q) (by simp) (by simp)))
        (.ax (A := 𝐗 (∼(q) 𝐔 q)) (by simp) (by simp)))
      (.ax (A := (∼(q) 𝐔 q)) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (q : Formula AP) :
    ([(∼(q) 𝐔 q)] ⊢ [𝐅 (q)]) ∧ ([𝐅 (q)] ⊢ [(∼(q) 𝐔 q)]) :=
  Candidate.candidate q

#print axioms verified
