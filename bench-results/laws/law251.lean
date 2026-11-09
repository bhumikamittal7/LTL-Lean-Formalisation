import LTL

open LTL

-- LTL law 251: ¬p U q ∨ ¬q U p ≈ ◇ (p ∨ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([((∼(p) 𝐔 q) ⋎ (∼(q) 𝐔 p))] ⊢ [𝐅 ((p ⋎ q))]) ∧ ([𝐅 ((p ⋎ q))] ⊢ [((∼(p) 𝐔 q) ⋎ (∼(q) 𝐔 p))]) := by
  constructor
  · refine Derives.orL (A := (∼(p) 𝐔 q)) (B := (∼(q) 𝐔 p)) (by simp) ?_ ?_
    · refine Derives.untilL (A := ∼(p)) (B := q) (I := 𝐅 (p ⋎ q)) (by simp) ?_ ?_ ?_
      · refine Derives.evR (A := p ⋎ q) (by simp) ?_
        refine Derives.orR (A := p) (B := q) (by simp) ?_
        exact .ax (A := q) (by simp) (by simp)
      · refine Derives.evR (A := p ⋎ q) (by simp) ?_
        exact .ax (A := 𝐗 (𝐅 (p ⋎ q))) (by simp) (by simp)
      · exact .ax (A := 𝐅 (p ⋎ q)) (by simp) (by simp)
    · refine Derives.untilL (A := ∼(q)) (B := p) (I := 𝐅 (p ⋎ q)) (by simp) ?_ ?_ ?_
      · refine Derives.evR (A := p ⋎ q) (by simp) ?_
        refine Derives.orR (A := p) (B := q) (by simp) ?_
        exact .ax (A := p) (by simp) (by simp)
      · refine Derives.evR (A := p ⋎ q) (by simp) ?_
        exact .ax (A := 𝐗 (𝐅 (p ⋎ q))) (by simp) (by simp)
      · exact .ax (A := 𝐅 (p ⋎ q)) (by simp) (by simp)
  · refine Derives.evL (A := p ⋎ q) (I := ((∼(p) 𝐔 q) ⋎ (∼(q) 𝐔 p))) (by simp) ?_ ?_ ?_
    · refine Derives.orL (A := p) (B := q) (by simp) ?_ ?_
      · refine Derives.orR (A := (∼(p) 𝐔 q)) (B := (∼(q) 𝐔 p)) (by simp) ?_
        refine Derives.untilR (A := ∼(q)) (B := p) (by simp) ?_ ?_
        · exact .ax (A := p) (by simp) (by simp)
        · exact .ax (A := p) (by simp) (by simp)
      · refine Derives.orR (A := (∼(p) 𝐔 q)) (B := (∼(q) 𝐔 p)) (by simp) ?_
        refine Derives.untilR (A := ∼(p)) (B := q) (by simp) ?_ ?_
        · exact .ax (A := q) (by simp) (by simp)
        · exact .ax (A := q) (by simp) (by simp)
    · refine Derives.orR (A := (∼(p) 𝐔 q)) (B := (∼(q) 𝐔 p)) (by simp) ?_
      refine Derives.untilR (A := ∼(p)) (B := q) (by simp) ?_ ?_
      · refine Derives.untilR (A := ∼(q)) (B := p) (by simp) ?_ ?_
        · refine Derives.negR (A := p) (by simp) ?_
          exact .ax (A := p) (by simp) (by simp)
        · refine Derives.negR (A := p) (by simp) ?_
          exact .ax (A := p) (by simp) (by simp)
      · refine Derives.untilR (A := ∼(q)) (B := p) (by simp) ?_ ?_
        · refine Derives.negR (A := q) (by simp) ?_
          exact .ax (A := q) (by simp) (by simp)
        · refine Derives.next (Γ' := [((∼(p) 𝐔 q) ⋎ (∼(q) 𝐔 p))])
            (Δ' := [(∼(p) 𝐔 q), (∼(q) 𝐔 p)]) ?_ (by simp) (by simp)
          refine Derives.orL (A := (∼(p) 𝐔 q)) (B := (∼(q) 𝐔 p)) (by simp) ?_ ?_
          · exact .ax (A := (∼(p) 𝐔 q)) (by simp) (by simp)
          · exact .ax (A := (∼(q) 𝐔 p)) (by simp) (by simp)
    · exact .ax (A := ((∼(p) 𝐔 q) ⋎ (∼(q) 𝐔 p))) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([((∼(p) 𝐔 q) ⋎ (∼(q) 𝐔 p))] ⊢ [𝐅 ((p ⋎ q))]) ∧ ([𝐅 ((p ⋎ q))] ⊢ [((∼(p) 𝐔 q) ⋎ (∼(q) 𝐔 p))]) :=
  Candidate.candidate p q

#print axioms verified
