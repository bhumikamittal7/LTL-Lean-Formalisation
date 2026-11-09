import LTL

open LTL

-- LTL law 155: ◯ □ ◇ p ≈ □ ◇ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem dir2_helper {AP : Type} (p : Formula AP) :
    [𝐆 (𝐅 (p))] ⊢ [𝐗 (𝐆 (𝐅 (p)))] :=
  Derives.alwaysL (A := 𝐅 p) (by simp)
    (Derives.ax (A := 𝐗 (𝐆 (𝐅 p))) (by simp) (by simp))

theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐗 (𝐆 (𝐅 (p)))] ⊢ [𝐆 (𝐅 (p))]) ∧ ([𝐆 (𝐅 (p))] ⊢ [𝐗 (𝐆 (𝐅 (p)))]) :=
  ⟨Derives.alwaysR (A := 𝐅 p) (I := 𝐗 (𝐆 (𝐅 p))) (by simp)
      (Derives.ax (A := 𝐗 (𝐆 (𝐅 p))) (by simp) (by simp))
      (Derives.step (Γ' := [𝐆 (𝐅 p)]) (B := 𝐗 (𝐆 (𝐅 p))) (dir2_helper p) (by simp) (by simp))
      (Derives.evR (A := p) (by simp)
        (Derives.step (Γ' := [𝐆 (𝐅 p)]) (B := 𝐅 p)
          (Derives.alwaysL (A := 𝐅 p) (by simp)
            (Derives.ax (A := 𝐅 p) (by simp) (by simp)))
          (by simp) (by simp))),
   dir2_helper p⟩

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐗 (𝐆 (𝐅 (p)))] ⊢ [𝐆 (𝐅 (p))]) ∧ ([𝐆 (𝐅 (p))] ⊢ [𝐗 (𝐆 (𝐅 (p)))]) :=
  Candidate.candidate p

#print axioms verified
