import LTL

open LTL

-- LTL law 156: ◯ ◇ □ p ≈ ◇ □ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem ltl_dir1_helper {AP : Type} (p : Formula AP) :
    [𝐗 (𝐅 (𝐆 (p)))] ⊢ [𝐅 (𝐆 (p))] :=
  Derives.evR (A := 𝐆 p) (by simp)
    (Derives.ax (A := 𝐗 (𝐅 (𝐆 p))) (by simp) (by simp))

theorem ltl_base_helper {AP : Type} (p : Formula AP) :
    [𝐆 p] ⊢ [𝐅 (𝐆 (p))] :=
  Derives.evR (A := 𝐆 p) (by simp)
    (Derives.ax (A := 𝐆 p) (by simp) (by simp))

theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐗 (𝐅 (𝐆 (p)))] ⊢ [𝐅 (𝐆 (p))]) ∧ ([𝐅 (𝐆 (p))] ⊢ [𝐗 (𝐅 (𝐆 (p)))]) := by
  refine ⟨ltl_dir1_helper p, ?_⟩
  exact Derives.evL (A := 𝐆 p) (I := 𝐗 (𝐅 (𝐆 p))) (by simp)
    (Derives.alwaysL (A := p) (by simp)
      (Derives.step (Γ' := [𝐆 p]) (ltl_base_helper p) (by simp) (by simp)))
    (Derives.step (Γ' := [𝐗 (𝐅 (𝐆 p))]) (ltl_dir1_helper p) (by simp) (by simp))
    (Derives.ax (A := 𝐗 (𝐅 (𝐆 p))) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐗 (𝐅 (𝐆 (p)))] ⊢ [𝐅 (𝐆 (p))]) ∧ ([𝐅 (𝐆 (p))] ⊢ [𝐗 (𝐅 (𝐆 (p)))]) :=
  Candidate.candidate p

#print axioms verified
