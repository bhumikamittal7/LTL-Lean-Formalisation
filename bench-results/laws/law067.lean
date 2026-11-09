import LTL

open LTL

-- LTL law 67: □ p ≈ p ∧ ◯ p ∧ ◯ □ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐆 (p)] ⊢ [(p ⋏ (𝐗 (p) ⋏ 𝐗 (𝐆 (p))))]) ∧ ([(p ⋏ (𝐗 (p) ⋏ 𝐗 (𝐆 (p))))] ⊢ [𝐆 (p)]) := by
  constructor
  · refine Derives.alwaysL (A := p) (by simp) ?_
    refine Derives.andR (A := p) (B := 𝐗 p ⋏ 𝐗 (𝐆 p)) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · refine Derives.andR (A := 𝐗 p) (B := 𝐗 (𝐆 p)) (by simp) ?_ ?_
      · refine Derives.step (Γ' := [𝐆 p]) (B := p) ?_ (by simp) (by simp)
        refine Derives.alwaysL (A := p) (by simp) ?_
        exact .ax (A := p) (by simp) (by simp)
      · exact .ax (A := 𝐗 (𝐆 p)) (by simp) (by simp)
  · refine Derives.alwaysR (A := p) (I := p ⋏ 𝐗 (𝐆 p)) (by simp) ?_ ?_ ?_
    · refine Derives.andL (A := p) (B := 𝐗 p ⋏ 𝐗 (𝐆 p)) (by simp) ?_
      refine Derives.andL (A := 𝐗 p) (B := 𝐗 (𝐆 p)) (by simp) ?_
      refine Derives.andR (A := p) (B := 𝐗 (𝐆 p)) (by simp) ?_ ?_
      · exact .ax (A := p) (by simp) (by simp)
      · exact .ax (A := 𝐗 (𝐆 p)) (by simp) (by simp)
    · refine Derives.andL (A := p) (B := 𝐗 (𝐆 p)) (by simp) ?_
      refine Derives.step (Γ' := [𝐆 p]) (B := p ⋏ 𝐗 (𝐆 p)) ?_ (by simp) (by simp)
      refine Derives.alwaysL (A := p) (by simp) ?_
      refine Derives.andR (A := p) (B := 𝐗 (𝐆 p)) (by simp) ?_ ?_
      · exact .ax (A := p) (by simp) (by simp)
      · exact .ax (A := 𝐗 (𝐆 p)) (by simp) (by simp)
    · refine Derives.andL (A := p) (B := 𝐗 (𝐆 p)) (by simp) ?_
      exact .ax (A := p) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐆 (p)] ⊢ [(p ⋏ (𝐗 (p) ⋏ 𝐗 (𝐆 (p))))]) ∧ ([(p ⋏ (𝐗 (p) ⋏ 𝐗 (𝐆 (p))))] ⊢ [𝐆 (p)]) :=
  Candidate.candidate p

#print axioms verified
