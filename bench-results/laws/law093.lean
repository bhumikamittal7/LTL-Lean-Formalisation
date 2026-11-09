import LTL

open LTL

-- LTL law 93: □ p ∧ ◇ ¬p ≈ ⊥
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([(𝐆 (p) ⋏ 𝐅 (∼(p)))] ⊢ [⊥ₗ]) ∧ ([⊥ₗ] ⊢ [(𝐆 (p) ⋏ 𝐅 (∼(p)))]) := by
  refine ⟨?_, Derives.botL (by simp)⟩
  refine Derives.andL (A := 𝐆 p) (B := 𝐅 (∼p)) (by simp) ?_
  refine Derives.evL (A := ∼p) (I := ∼(𝐆 p)) (by simp) ?_ ?_ ?_
  · refine Derives.negR (A := 𝐆 p) (by simp) ?_
    refine Derives.alwaysL (A := p) (by simp) ?_
    refine Derives.negL (A := p) (by simp) ?_
    exact Derives.ax (A := p) (by simp) (by simp)
  · refine Derives.negR (A := 𝐆 p) (by simp) ?_
    refine Derives.alwaysL (A := p) (by simp) ?_
    refine Derives.next (Γ' := [∼(𝐆 p), 𝐆 p]) (Δ' := []) ?_ (by simp) (by simp)
    refine Derives.negL (A := 𝐆 p) (by simp) ?_
    exact Derives.ax (A := 𝐆 p) (by simp) (by simp)
  · refine Derives.negL (A := 𝐆 p) (by simp) ?_
    exact Derives.ax (A := 𝐆 p) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(𝐆 (p) ⋏ 𝐅 (∼(p)))] ⊢ [⊥ₗ]) ∧ ([⊥ₗ] ⊢ [(𝐆 (p) ⋏ 𝐅 (∼(p)))]) :=
  Candidate.candidate p

#print axioms verified
