import LTL

open LTL

-- LTL law 79: □ p ⟹ ◯ □ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    [𝐆 (p)] ⊢ [𝐗 (𝐆 (p))] :=
  Derives.alwaysL (A := p) (by simp)
    (Derives.ax (A := 𝐗 (𝐆 (p))) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    [𝐆 (p)] ⊢ [𝐗 (𝐆 (p))] :=
  Candidate.candidate p

#print axioms verified
