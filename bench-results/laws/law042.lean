import LTL

open LTL

-- LTL law 42: p U q ⟹ ◇ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [(p 𝐔 q)] ⊢ [𝐅 (q)] :=
  Derives.untilL (A := p) (B := q) (I := 𝐅 q) (by simp)
    (Derives.evR (A := q) (by simp) (.ax (A := q) (by simp) (by simp)))
    (Derives.evR (A := q) (by simp) (.ax (A := 𝐗 (𝐅 q)) (by simp) (by simp)))
    (.ax (A := 𝐅 q) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [(p 𝐔 q)] ⊢ [𝐅 (q)] :=
  Candidate.candidate p q

#print axioms verified
