import LTL

open LTL

-- LTL law 78: □ p ⟹ ◯ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    [𝐆 (p)] ⊢ [𝐗 (p)] :=
  Derives.alwaysL (A := p) (by simp)
    (Derives.step (Γ' := [𝐆 p]) (B := p)
      (Derives.alwaysL (A := p) (by simp)
        (Derives.ax (A := p) (by simp) (by simp)))
      (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    [𝐆 (p)] ⊢ [𝐗 (p)] :=
  Candidate.candidate p

#print axioms verified
