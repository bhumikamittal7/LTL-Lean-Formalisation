import LTL

open LTL

-- LTL law 46: p ⟹ ◇ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    [p] ⊢ [𝐅 (p)] :=
  Derives.evR (A := p) (by simp) (Derives.ax (A := p) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    [p] ⊢ [𝐅 (p)] :=
  Candidate.candidate p

#print axioms verified
