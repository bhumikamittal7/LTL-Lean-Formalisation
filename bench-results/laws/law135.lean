import LTL

open LTL

-- LTL law 135: □ (p ⇒ ◯ ¬p) ⟹ (p ⇒ ¬□ p)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    [𝐆 ((p ⇒ 𝐗 (∼(p))))] ⊢ [(p ⇒ ∼(𝐆 (p)))] := by
  refine Derives.impR (A := p) (B := ∼(𝐆 p)) (by simp) ?_
  refine Derives.negR (A := 𝐆 p) (by simp) ?_
  refine Derives.alwaysL (A := (p ⇒ 𝐗 (∼p))) (by simp) ?_
  refine Derives.impL (A := p) (B := 𝐗 (∼p)) (by simp) ?_ ?_
  · exact Derives.ax (A := p) (by simp) (by simp)
  · refine Derives.alwaysL (A := p) (by simp) ?_
    refine Derives.next (Γ' := [∼p, 𝐆 p]) (Δ' := []) ?_ (by simp) (by simp)
    refine Derives.negL (A := p) (by simp) ?_
    refine Derives.alwaysL (A := p) (by simp) ?_
    exact Derives.ax (A := p) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    [𝐆 ((p ⇒ 𝐗 (∼(p))))] ⊢ [(p ⇒ ∼(𝐆 (p)))] :=
  Candidate.candidate p

#print axioms verified
