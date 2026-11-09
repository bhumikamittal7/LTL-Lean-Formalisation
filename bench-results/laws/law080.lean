import LTL

open LTL

-- LTL law 80: □ p ⟹ □ ◯ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    [𝐆 (p)] ⊢ [𝐆 (𝐗 (p))] :=
  Derives.alwaysR (A := 𝐗 p) (I := 𝐆 p) (by simp)
    (Derives.ax (A := 𝐆 p) (by simp) (by simp))
    (Derives.alwaysL (A := p) (by simp)
      (Derives.ax (A := 𝐗 (𝐆 p)) (by simp) (by simp)))
    (Derives.alwaysL (A := p) (by simp)
      (Derives.step (Γ' := [𝐆 p]) (B := p)
        (Derives.alwaysL (A := p) (by simp)
          (Derives.ax (A := p) (by simp) (by simp)))
        (by simp) (by simp)))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    [𝐆 (p)] ⊢ [𝐆 (𝐗 (p))] :=
  Candidate.candidate p

#print axioms verified
