import LTL

open LTL

-- LTL law 147: ◇ □ p ∧ ◇ □ ¬p ≈ ⊥
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([(𝐅 (𝐆 (p)) ⋏ 𝐅 (𝐆 (∼(p))))] ⊢ [⊥ₗ]) ∧ ([⊥ₗ] ⊢ [(𝐅 (𝐆 (p)) ⋏ 𝐅 (𝐆 (∼(p))))]) := by
  refine ⟨?_, Derives.botL (by simp)⟩
  have h1 : [𝐆 p] ⊢ [∼(𝐅 (𝐆 (∼p)))] := by
    refine Derives.negR (A := 𝐅 (𝐆 (∼p))) (by simp) ?_
    refine Derives.evL (A := 𝐆 (∼p)) (I := ∼(𝐆 p)) (by simp) ?_ ?_ ?_
    · refine Derives.negR (A := 𝐆 p) (by simp) ?_
      refine Derives.alwaysL (A := p) (by simp) ?_
      refine Derives.alwaysL (A := ∼p) (by simp) ?_
      exact Derives.negL (A := p) (by simp) (Derives.ax (A := p) (by simp) (by simp))
    · refine Derives.negR (A := 𝐆 p) (by simp) ?_
      refine Derives.alwaysL (A := p) (by simp) ?_
      exact Derives.next (Γ' := [∼(𝐆 p), 𝐆 p]) (Δ' := [])
        (Derives.negL (A := 𝐆 p) (by simp) (Derives.ax (A := 𝐆 p) (by simp) (by simp)))
        (by simp) (by simp)
    · exact Derives.negL (A := 𝐆 p) (by simp) (Derives.ax (A := 𝐆 p) (by simp) (by simp))
  have h2 : [𝐗 (∼(𝐅 (𝐆 (∼p))))] ⊢ [∼(𝐅 (𝐆 (∼p)))] := by
    refine Derives.negR (A := 𝐅 (𝐆 (∼p))) (by simp) ?_
    refine Derives.evL (A := 𝐆 (∼p)) (I := 𝐗 (𝐅 (𝐆 (∼p)))) (by simp) ?_ ?_ ?_
    · refine Derives.alwaysL (A := ∼p) (by simp) ?_
      exact Derives.step (Γ' := [𝐆 (∼p)]) (B := 𝐅 (𝐆 (∼p)))
        (Derives.evR (A := 𝐆 (∼p)) (by simp)
          (Derives.ax (A := 𝐆 (∼p)) (by simp) (by simp)))
        (by simp) (by simp)
    · exact Derives.step (Γ' := [𝐗 (𝐅 (𝐆 (∼p)))]) (B := 𝐅 (𝐆 (∼p)))
        (Derives.evR (A := 𝐆 (∼p)) (by simp)
          (Derives.ax (A := 𝐗 (𝐅 (𝐆 (∼p)))) (by simp) (by simp)))
        (by simp) (by simp)
    · exact Derives.next (Γ' := [𝐅 (𝐆 (∼p)), ∼(𝐅 (𝐆 (∼p)))]) (Δ' := [])
        (Derives.negL (A := 𝐅 (𝐆 (∼p))) (by simp)
          (Derives.ax (A := 𝐅 (𝐆 (∼p))) (by simp) (by simp)))
        (by simp) (by simp)
  refine Derives.andL (A := 𝐅 (𝐆 p)) (B := 𝐅 (𝐆 (∼p))) (by simp) ?_
  refine Derives.evL (A := 𝐆 p) (I := ∼(𝐅 (𝐆 (∼p)))) (by simp) h1 h2 ?_
  exact Derives.negL (A := 𝐅 (𝐆 (∼p))) (by simp)
    (Derives.ax (A := 𝐅 (𝐆 (∼p))) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(𝐅 (𝐆 (p)) ⋏ 𝐅 (𝐆 (∼(p))))] ⊢ [⊥ₗ]) ∧ ([⊥ₗ] ⊢ [(𝐅 (𝐆 (p)) ⋏ 𝐅 (𝐆 (∼(p))))]) :=
  Candidate.candidate p

#print axioms verified
