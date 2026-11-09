import LTL

open LTL

-- LTL law 151: ◇ □ ◇ p ≈ □ ◇ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem gfp_to_fgfp {AP : Type} (p : Formula AP) : [𝐆 (𝐅 p)] ⊢ [𝐅 (𝐆 (𝐅 p))] :=
  Derives.evR (A := 𝐆 (𝐅 p)) (by simp)
    (Derives.ax (A := 𝐆 (𝐅 p)) (by simp) (by simp))

theorem fgfp_fp {AP : Type} (p : Formula AP) : [𝐅 (𝐆 (𝐅 p))] ⊢ [𝐅 p] :=
  Derives.evL (A := 𝐆 (𝐅 p)) (I := 𝐅 p) (by simp)
    (Derives.alwaysL (A := 𝐅 p) (by simp)
      (Derives.ax (A := 𝐅 p) (by simp) (by simp)))
    (Derives.evR (A := p) (by simp)
      (Derives.ax (A := 𝐗 (𝐅 p)) (by simp) (by simp)))
    (Derives.ax (A := 𝐅 p) (by simp) (by simp))

theorem fgfp_xfgfp {AP : Type} (p : Formula AP) :
    [𝐅 (𝐆 (𝐅 p))] ⊢ [𝐗 (𝐅 (𝐆 (𝐅 p)))] :=
  Derives.evL (A := 𝐆 (𝐅 p)) (I := 𝐗 (𝐅 (𝐆 (𝐅 p)))) (by simp)
    (Derives.alwaysL (A := 𝐅 p) (by simp)
      (Derives.step (Γ' := [𝐆 (𝐅 p)]) (B := 𝐅 (𝐆 (𝐅 p)))
        (gfp_to_fgfp p) (by simp) (by simp)))
    (Derives.step (Γ' := [𝐗 (𝐅 (𝐆 (𝐅 p)))]) (B := 𝐅 (𝐆 (𝐅 p)))
      (Derives.evR (A := 𝐆 (𝐅 p)) (by simp)
        (Derives.ax (A := 𝐗 (𝐅 (𝐆 (𝐅 p)))) (by simp) (by simp)))
      (by simp) (by simp))
    (Derives.ax (A := 𝐗 (𝐅 (𝐆 (𝐅 p)))) (by simp) (by simp))

theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐅 (𝐆 (𝐅 (p)))] ⊢ [𝐆 (𝐅 (p))]) ∧ ([𝐆 (𝐅 (p))] ⊢ [𝐅 (𝐆 (𝐅 (p)))]) :=
  ⟨Derives.alwaysR (A := 𝐅 p) (I := 𝐅 (𝐆 (𝐅 p))) (by simp)
      (Derives.ax (A := 𝐅 (𝐆 (𝐅 p))) (by simp) (by simp))
      (fgfp_xfgfp p)
      (fgfp_fp p),
   gfp_to_fgfp p⟩

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐅 (𝐆 (𝐅 (p)))] ⊢ [𝐆 (𝐅 (p))]) ∧ ([𝐆 (𝐅 (p))] ⊢ [𝐅 (𝐆 (𝐅 (p)))]) :=
  Candidate.candidate p

#print axioms verified
