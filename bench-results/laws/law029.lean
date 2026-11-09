import LTL

open LTL

-- LTL law 29: q ⟹ p U q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [q] ⊢ [(p 𝐔 q)] :=
  .untilR (A := p) (B := q) (by simp)
    (.ax (A := q) (by simp) (by simp))
    (.ax (A := q) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [q] ⊢ [(p 𝐔 q)] :=
  Candidate.candidate p q

#print axioms verified
