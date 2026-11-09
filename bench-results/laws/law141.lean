import LTL

open LTL

-- LTL law 141: p U □ p ≈ □ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem helper_unfold {AP : Type} (p : Formula AP) :
    [𝐆 p] ⊢ [p ⋏ 𝐗 (𝐆 p)] :=
  Derives.alwaysL (A := p) (by simp)
    (Derives.andR (A := p) (B := 𝐗 (𝐆 p)) (by simp)
      (Derives.ax (A := p) (by simp) (by simp))
      (Derives.ax (A := 𝐗 (𝐆 p)) (by simp) (by simp)))

theorem helper_step {AP : Type} (p : Formula AP) :
    [p, 𝐗 (𝐆 p)] ⊢ [𝐆 p] :=
  Derives.alwaysR (A := p) (p ⋏ 𝐗 (𝐆 p)) (by simp)
    (Derives.andR (A := p) (B := 𝐗 (𝐆 p)) (by simp)
      (Derives.ax (A := p) (by simp) (by simp))
      (Derives.ax (A := 𝐗 (𝐆 p)) (by simp) (by simp)))
    (Derives.andL (A := p) (B := 𝐗 (𝐆 p)) (by simp)
      (Derives.step (Γ' := [𝐆 p]) (B := p ⋏ 𝐗 (𝐆 p)) (helper_unfold p) (by simp) (by simp)))
    (Derives.andL (A := p) (B := 𝐗 (𝐆 p)) (by simp)
      (Derives.ax (A := p) (by simp) (by simp)))

theorem candidate {AP : Type} (p : Formula AP) :
    ([(p 𝐔 𝐆 (p))] ⊢ [𝐆 (p)]) ∧ ([𝐆 (p)] ⊢ [(p 𝐔 𝐆 (p))]) :=
  ⟨Derives.untilL (A := p) (B := 𝐆 p) (𝐆 p) (by simp)
      (Derives.ax (A := 𝐆 p) (by simp) (by simp))
      (helper_step p)
      (Derives.ax (A := 𝐆 p) (by simp) (by simp)),
   Derives.untilR (A := p) (B := 𝐆 p) (by simp)
      (Derives.ax (A := 𝐆 p) (by simp) (by simp))
      (Derives.ax (A := 𝐆 p) (by simp) (by simp))⟩

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(p 𝐔 𝐆 (p))] ⊢ [𝐆 (p)]) ∧ ([𝐆 (p)] ⊢ [(p 𝐔 𝐆 (p))]) :=
  Candidate.candidate p

#print axioms verified
