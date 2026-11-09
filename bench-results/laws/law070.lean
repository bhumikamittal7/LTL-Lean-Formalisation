import LTL

open LTL

-- LTL law 70: ◇ p ∧ □ p ≈ □ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([(𝐅 (p) ⋏ 𝐆 (p))] ⊢ [𝐆 (p)]) ∧ ([𝐆 (p)] ⊢ [(𝐅 (p) ⋏ 𝐆 (p))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.andL (A := 𝐅 p) (B := 𝐆 p) (by simp)
      (Derives.ax (A := 𝐆 p) (by simp) (by simp))
  · exact Derives.andR (A := 𝐅 p) (B := 𝐆 p) (by simp)
      (Derives.evR (A := p) (by simp)
        (Derives.alwaysL (A := p) (by simp)
          (Derives.ax (A := p) (by simp) (by simp))))
      (Derives.ax (A := 𝐆 p) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(𝐅 (p) ⋏ 𝐆 (p))] ⊢ [𝐆 (p)]) ∧ ([𝐆 (p)] ⊢ [(𝐅 (p) ⋏ 𝐆 (p))]) :=
  Candidate.candidate p

#print axioms verified
