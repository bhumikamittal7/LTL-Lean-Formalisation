import LTL

open LTL

-- LTL law 235: □ p ⟹ p U q ∨ □ ¬q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [((p 𝐔 q) ⋎ 𝐆 (∼(q)))] := by
  refine Derives.orR (A := p 𝐔 q) (B := 𝐆 (∼q)) (by simp) ?_
  refine Derives.alwaysR (A := ∼q) (𝐆 p ⋏ ∼(p 𝐔 q)) (by simp) ?_ ?_ ?_
  · refine Derives.andR (A := 𝐆 p) (B := ∼(p 𝐔 q)) (by simp)
      (Derives.ax (A := 𝐆 p) (by simp) (by simp)) ?_
    exact Derives.negR (A := p 𝐔 q) (by simp) (Derives.ax (A := p 𝐔 q) (by simp) (by simp))
  · refine Derives.andL (A := 𝐆 p) (B := ∼(p 𝐔 q)) (by simp) ?_
    refine Derives.alwaysL (A := p) (by simp) ?_
    refine Derives.negL (A := p 𝐔 q) (by simp) ?_
    refine Derives.untilR (A := p) (B := q) (by simp)
      (Derives.ax (A := p) (by simp) (by simp)) ?_
    refine Derives.next (Γ' := [𝐆 p]) (Δ' := [p 𝐔 q, 𝐆 p ⋏ ∼(p 𝐔 q)]) ?_ (by simp) (by simp)
    refine Derives.andR (A := 𝐆 p) (B := ∼(p 𝐔 q)) (by simp)
      (Derives.ax (A := 𝐆 p) (by simp) (by simp)) ?_
    exact Derives.negR (A := p 𝐔 q) (by simp) (Derives.ax (A := p 𝐔 q) (by simp) (by simp))
  · refine Derives.andL (A := 𝐆 p) (B := ∼(p 𝐔 q)) (by simp) ?_
    refine Derives.negR (A := q) (by simp) ?_
    refine Derives.negL (A := p 𝐔 q) (by simp) ?_
    exact Derives.untilR (A := p) (B := q) (by simp)
      (Derives.ax (A := q) (by simp) (by simp))
      (Derives.ax (A := q) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [((p 𝐔 q) ⋎ 𝐆 (∼(q)))] :=
  Candidate.candidate p q

#print axioms verified
