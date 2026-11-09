import LTL

open LTL

-- LTL law 54: □ p ≈ ¬◇ ¬p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐆 (p)] ⊢ [∼(𝐅 (∼(p)))]) ∧ ([∼(𝐅 (∼(p)))] ⊢ [𝐆 (p)]) := by
  refine ⟨?_, ?_⟩
  · -- □p ⟹ ¬◇¬p
    exact
      .negR (A := 𝐅 (∼p)) (by simp)
        (.evL (A := ∼p) (I := ∼(𝐆 p)) (by simp)
          -- [∼p] ⊢ [∼𝐆p]
          (.negR (A := 𝐆 p) (by simp)
            (.alwaysL (A := p) (by simp)
              (.negL (A := p) (by simp) (.ax (A := p) (by simp) (by simp)))))
          -- [𝐗 ∼𝐆p] ⊢ [∼𝐆p]
          (.negR (A := 𝐆 p) (by simp)
            (.alwaysL (A := p) (by simp)
              (.next (Γ' := [∼(𝐆 p), 𝐆 p]) (Δ' := [])
                (.negL (A := 𝐆 p) (by simp) (.ax (A := 𝐆 p) (by simp) (by simp)))
                (by simp) (by simp))))
          -- ∼𝐆p :: Γ ⊢ Δ
          (.negL (A := 𝐆 p) (by simp) (.ax (A := 𝐆 p) (by simp) (by simp))))
  · -- ¬◇¬p ⟹ □p
    exact
      .alwaysR (A := p) (I := ∼(𝐅 (∼p))) (by simp)
        (.ax (A := ∼(𝐅 (∼p))) (by simp) (by simp))
        (.negL (A := 𝐅 (∼p)) (by simp)
          (.evR (A := ∼p) (by simp)
            (.next (Γ' := []) (Δ' := [𝐅 (∼p), ∼(𝐅 (∼p))])
              (.negR (A := 𝐅 (∼p)) (by simp)
                (.ax (A := 𝐅 (∼p)) (by simp) (by simp)))
              (by simp) (by simp))))
        (.negL (A := 𝐅 (∼p)) (by simp)
          (.evR (A := ∼p) (by simp)
            (.negR (A := p) (by simp) (.ax (A := p) (by simp) (by simp)))))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐆 (p)] ⊢ [∼(𝐅 (∼(p)))]) ∧ ([∼(𝐅 (∼(p)))] ⊢ [𝐆 (p)]) :=
  Candidate.candidate p

#print axioms verified
