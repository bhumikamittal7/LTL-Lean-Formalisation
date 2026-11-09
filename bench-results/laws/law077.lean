import LTL

open LTL

-- LTL law 77: □ p ⟹ ◇ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    [𝐆 (p)] ⊢ [𝐅 (p)] :=
  -- Unfold 𝐆 p on the left: the premise has p :: 𝐗 (𝐆 p) :: [𝐆 p] ⊢ [𝐅 p].
  Derives.alwaysL (A := p) (by simp)
    -- Unfold 𝐅 p on the right: the premise has Δ = p :: 𝐗 (𝐅 p) :: [𝐅 p].
    (Derives.evR (A := p) (by simp)
      -- p is now on both sides, so close with ax.
      (Derives.ax (A := p) (by simp) (by simp)))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    [𝐆 (p)] ⊢ [𝐅 (p)] :=
  Candidate.candidate p

#print axioms verified
