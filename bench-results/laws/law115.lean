import LTL

open LTL

-- LTL law 115: □ p ⟹ (◯ q ⇒ ◯ (p ≡ q))
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐗 (q) ⇒ 𝐗 (((p ⇒ q) ⋏ (q ⇒ p))))] := by
  refine Derives.impR (A := 𝐗 q) (B := 𝐗 ((p ⇒ q) ⋏ (q ⇒ p))) (by simp) ?_
  refine Derives.alwaysL (A := p) (by simp) ?_
  refine Derives.step (Γ' := [𝐆 p, q]) (B := (p ⇒ q) ⋏ (q ⇒ p)) ?_ (by simp) (by simp)
  refine Derives.andR (A := p ⇒ q) (B := q ⇒ p) (by simp) ?_ ?_
  · refine Derives.impR (A := p) (B := q) (by simp) ?_
    exact Derives.ax (A := q) (by simp) (by simp)
  · refine Derives.impR (A := q) (B := p) (by simp) ?_
    refine Derives.alwaysL (A := p) (by simp) ?_
    exact Derives.ax (A := p) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐗 (q) ⇒ 𝐗 (((p ⇒ q) ⋏ (q ⇒ p))))] :=
  Candidate.candidate p q

#print axioms verified
