import LTL

open LTL

-- LTL law 145: ◇ □ p ⟹ □ ◇ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    [𝐅 (𝐆 (p))] ⊢ [𝐆 (𝐅 (p))] := by
  refine Derives.alwaysR (A := 𝐅 p) (I := 𝐅 (𝐆 p)) (by simp) ?_ ?_ ?_
  · exact .ax (A := 𝐅 (𝐆 p)) (by simp) (by simp)
  · refine Derives.evL (A := 𝐆 p) (I := 𝐗 (𝐅 (𝐆 p))) (by simp) ?_ ?_ ?_
    · refine Derives.alwaysL (A := p) (by simp) ?_
      refine Derives.step (Γ' := [𝐆 p]) (B := 𝐅 (𝐆 p)) ?_ (by simp) (by simp)
      refine Derives.evR (A := 𝐆 p) (by simp) ?_
      exact .ax (A := 𝐆 p) (by simp) (by simp)
    · refine Derives.step (Γ' := [𝐗 (𝐅 (𝐆 p))]) (B := 𝐅 (𝐆 p)) ?_ (by simp) (by simp)
      refine Derives.evR (A := 𝐆 p) (by simp) ?_
      exact .ax (A := 𝐗 (𝐅 (𝐆 p))) (by simp) (by simp)
    · exact .ax (A := 𝐗 (𝐅 (𝐆 p))) (by simp) (by simp)
  · refine Derives.evL (A := 𝐆 p) (I := 𝐅 p) (by simp) ?_ ?_ ?_
    · refine Derives.alwaysL (A := p) (by simp) ?_
      refine Derives.evR (A := p) (by simp) ?_
      exact .ax (A := p) (by simp) (by simp)
    · refine Derives.evR (A := p) (by simp) ?_
      exact .ax (A := 𝐗 (𝐅 p)) (by simp) (by simp)
    · exact .ax (A := 𝐅 p) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    [𝐅 (𝐆 (p))] ⊢ [𝐆 (𝐅 (p))] :=
  Candidate.candidate p

#print axioms verified
