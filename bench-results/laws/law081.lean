import LTL

open LTL

-- LTL law 81: □ p ⟹ ¬(q U ¬p)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [∼((q 𝐔 ∼(p)))] := by
  refine Derives.negR (A := q 𝐔 ∼(p)) (by simp) ?_
  refine Derives.untilL (I := ∼(𝐆 p)) (A := q) (B := ∼(p)) (by simp) ?_ ?_ ?_
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

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [∼((q 𝐔 ∼(p)))] :=
  Candidate.candidate p q

#print axioms verified
