import LTL

open LTL

-- LTL law 3: ◯ p ≈ ¬◯ ¬p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐗 (p)] ⊢ [∼(𝐗 (∼(p)))]) ∧ ([∼(𝐗 (∼(p)))] ⊢ [𝐗 (p)]) := by
  refine ⟨?_, ?_⟩
  · exact .negR (A := 𝐗 (∼p)) (by simp)
      (.next (Γ' := [p, ∼p]) (Δ' := [])
        (.negL (A := p) (by simp) (.ax (A := p) (by simp) (by simp)))
        (by simp) (by simp))
  · exact .negL (A := 𝐗 (∼p)) (by simp)
      (.next (Γ' := []) (Δ' := [∼p, p])
        (.negR (A := p) (by simp) (.ax (A := p) (by simp) (by simp)))
        (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐗 (p)] ⊢ [∼(𝐗 (∼(p)))]) ∧ ([∼(𝐗 (∼(p)))] ⊢ [𝐗 (p)]) :=
  Candidate.candidate p

#print axioms verified
