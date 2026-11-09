import LTL

open LTL

-- LTL law 59: ◇ p ≈ ¬□ ¬p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐅 (p)] ⊢ [∼(𝐆 (∼(p)))]) ∧ ([∼(𝐆 (∼(p)))] ⊢ [𝐅 (p)]) := by
  refine ⟨?_, ?_⟩
  · refine Derives.evL (A := p) (I := ∼(𝐆 (∼(p)))) (by simp) ?_ ?_ ?_
    · exact .negR (A := 𝐆 (∼(p))) (by simp)
        (.alwaysL (A := ∼(p)) (by simp)
          (.negL (A := p) (by simp) (.ax (A := p) (by simp) (by simp))))
    · exact .negR (A := 𝐆 (∼(p))) (by simp)
        (.alwaysL (A := ∼(p)) (by simp)
          (.next (Γ' := [∼(𝐆 (∼(p))), 𝐆 (∼(p))]) (Δ' := [])
            (.negL (A := 𝐆 (∼(p))) (by simp)
              (.ax (A := 𝐆 (∼(p))) (by simp) (by simp)))
            (by simp) (by simp)))
    · exact .ax (A := ∼(𝐆 (∼(p)))) (by simp) (by simp)
  · refine Derives.negL (A := 𝐆 (∼(p))) (by simp) ?_
    refine Derives.alwaysR (A := ∼(p)) (I := ∼(𝐅 (p))) (by simp) ?_ ?_ ?_
    · exact .negR (A := 𝐅 (p)) (by simp) (.ax (A := 𝐅 (p)) (by simp) (by simp))
    · exact .negL (A := 𝐅 (p)) (by simp)
        (.evR (A := p) (by simp)
          (.next (Γ' := []) (Δ' := [𝐅 (p), ∼(𝐅 (p))])
            (.negR (A := 𝐅 (p)) (by simp) (.ax (A := 𝐅 (p)) (by simp) (by simp)))
            (by simp) (by simp)))
    · exact .negR (A := p) (by simp)
        (.negL (A := 𝐅 (p)) (by simp)
          (.evR (A := p) (by simp) (.ax (A := p) (by simp) (by simp))))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐅 (p)] ⊢ [∼(𝐆 (∼(p)))]) ∧ ([∼(𝐆 (∼(p)))] ⊢ [𝐅 (p)]) :=
  Candidate.candidate p

#print axioms verified
