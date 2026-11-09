import LTL

open LTL

-- LTL law 30: p ∧ q ⟹ p U q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [(p ⋏ q)] ⊢ [(p 𝐔 q)] :=
  Derives.andL (A := p) (B := q) (by simp)
    (Derives.untilR (A := p) (B := q) (by simp)
      (Derives.ax (A := q) (by simp) (by simp))
      (Derives.ax (A := q) (by simp) (by simp)))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [(p ⋏ q)] ⊢ [(p 𝐔 q)] :=
  Candidate.candidate p q

#print axioms verified
