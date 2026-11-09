import LTL

open LTL

-- LTL law 47: ◯ p ⟹ ◇ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    [𝐗 (p)] ⊢ [𝐅 (p)] :=
  .evR (A := p) (by simp)
    (Derives.step (Γ' := [p]) (B := 𝐅 p)
      (.evR (A := p) (by simp) (.ax (A := p) (by simp) (by simp)))
      (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    [𝐗 (p)] ⊢ [𝐅 (p)] :=
  Candidate.candidate p

#print axioms verified
