import LTL

open LTL

-- LTL law 63: ¬□ ◇ p ≈ ◇ □ ¬p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([∼(𝐆 (𝐅 (p)))] ⊢ [𝐅 (𝐆 (∼(p)))]) ∧ ([𝐅 (𝐆 (∼(p)))] ⊢ [∼(𝐆 (𝐅 (p)))]) := by
  constructor
  · refine Derives.negL (A := 𝐆 (𝐅 p)) (by simp) ?_
    refine Derives.alwaysR (A := 𝐅 p) (I := ∼(𝐅 (𝐆 (∼p)))) (by simp) ?_ ?_ ?_
    · refine Derives.negR (A := 𝐅 (𝐆 (∼p))) (by simp) ?_
      exact Derives.ax (A := 𝐅 (𝐆 (∼p))) (by simp) (by simp)
    · refine Derives.negL (A := 𝐅 (𝐆 (∼p))) (by simp) ?_
      refine Derives.evR (A := 𝐆 (∼p)) (by simp) ?_
      refine Derives.next (Γ' := []) (Δ' := [∼(𝐅 (𝐆 (∼p))), 𝐅 (𝐆 (∼p))]) ?_ (by simp) (by simp)
      refine Derives.negR (A := 𝐅 (𝐆 (∼p))) (by simp) ?_
      exact Derives.ax (A := 𝐅 (𝐆 (∼p))) (by simp) (by simp)
    · refine Derives.negL (A := 𝐅 (𝐆 (∼p))) (by simp) ?_
      refine Derives.evR (A := 𝐆 (∼p)) (by simp) ?_
      refine Derives.alwaysR (A := ∼p) (I := ∼(𝐅 p)) (by simp) ?_ ?_ ?_
      · refine Derives.negR (A := 𝐅 p) (by simp) ?_
        exact Derives.ax (A := 𝐅 p) (by simp) (by simp)
      · refine Derives.negL (A := 𝐅 p) (by simp) ?_
        refine Derives.evR (A := p) (by simp) ?_
        refine Derives.next (Γ' := []) (Δ' := [∼(𝐅 p), 𝐅 p]) ?_ (by simp) (by simp)
        refine Derives.negR (A := 𝐅 p) (by simp) ?_
        exact Derives.ax (A := 𝐅 p) (by simp) (by simp)
      · refine Derives.negR (A := p) (by simp) ?_
        refine Derives.negL (A := 𝐅 p) (by simp) ?_
        refine Derives.evR (A := p) (by simp) ?_
        exact Derives.ax (A := p) (by simp) (by simp)
  · refine Derives.negR (A := 𝐆 (𝐅 p)) (by simp) ?_
    refine Derives.evL (A := 𝐆 (∼p)) (I := ∼(𝐆 (𝐅 p))) (by simp) ?_ ?_ ?_
    · refine Derives.negR (A := 𝐆 (𝐅 p)) (by simp) ?_
      refine Derives.alwaysL (A := 𝐅 p) (by simp) ?_
      refine Derives.evL (A := p) (I := ∼(𝐆 (∼p))) (by simp) ?_ ?_ ?_
      · refine Derives.negR (A := 𝐆 (∼p)) (by simp) ?_
        refine Derives.alwaysL (A := ∼p) (by simp) ?_
        refine Derives.negL (A := p) (by simp) ?_
        exact Derives.ax (A := p) (by simp) (by simp)
      · refine Derives.negR (A := 𝐆 (∼p)) (by simp) ?_
        refine Derives.alwaysL (A := ∼p) (by simp) ?_
        refine Derives.next (Γ' := [∼(𝐆 (∼p)), 𝐆 (∼p)]) (Δ' := []) ?_ (by simp) (by simp)
        refine Derives.negL (A := 𝐆 (∼p)) (by simp) ?_
        exact Derives.ax (A := 𝐆 (∼p)) (by simp) (by simp)
      · refine Derives.negL (A := 𝐆 (∼p)) (by simp) ?_
        exact Derives.ax (A := 𝐆 (∼p)) (by simp) (by simp)
    · refine Derives.negR (A := 𝐆 (𝐅 p)) (by simp) ?_
      refine Derives.alwaysL (A := 𝐅 p) (by simp) ?_
      refine Derives.next (Γ' := [∼(𝐆 (𝐅 p)), 𝐆 (𝐅 p)]) (Δ' := []) ?_ (by simp) (by simp)
      refine Derives.negL (A := 𝐆 (𝐅 p)) (by simp) ?_
      exact Derives.ax (A := 𝐆 (𝐅 p)) (by simp) (by simp)
    · exact Derives.ax (A := ∼(𝐆 (𝐅 p))) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([∼(𝐆 (𝐅 (p)))] ⊢ [𝐅 (𝐆 (∼(p)))]) ∧ ([𝐅 (𝐆 (∼(p)))] ⊢ [∼(𝐆 (𝐅 (p)))]) :=
  Candidate.candidate p

#print axioms verified
