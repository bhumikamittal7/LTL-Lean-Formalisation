import LTL

open LTL

-- LTL law 51: ◯ ◇ p ≈ ◇ ◯ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem fx_helper {AP : Type} (p : Formula AP) :
    [𝐅 p] ⊢ [p, 𝐅 (𝐗 p)] :=
  Derives.evL (p ⋎ 𝐅 (𝐗 p)) (A := p) (by simp)
    (Derives.orR (A := p) (B := 𝐅 (𝐗 p)) (by simp)
      (Derives.ax (A := p) (by simp) (by simp)))
    (Derives.orR (A := p) (B := 𝐅 (𝐗 p)) (by simp)
      (Derives.evR (A := 𝐗 p) (by simp)
        (Derives.next (Γ' := [p ⋎ 𝐅 (𝐗 p)]) (Δ' := [p, 𝐅 (𝐗 p)])
          (Derives.orL (A := p) (B := 𝐅 (𝐗 p)) (by simp)
            (Derives.ax (A := p) (by simp) (by simp))
            (Derives.ax (A := 𝐅 (𝐗 p)) (by simp) (by simp)))
          (by simp) (by simp))))
    (Derives.orL (A := p) (B := 𝐅 (𝐗 p)) (by simp)
      (Derives.ax (A := p) (by simp) (by simp))
      (Derives.ax (A := 𝐅 (𝐗 p)) (by simp) (by simp)))

theorem fx_dir1 {AP : Type} (p : Formula AP) :
    [𝐗 (𝐅 p)] ⊢ [𝐅 (𝐗 p)] :=
  Derives.evR (A := 𝐗 p) (by simp)
    (Derives.next (Γ' := [𝐅 p]) (Δ' := [p, 𝐅 (𝐗 p)])
      (fx_helper p) (by simp) (by simp))

theorem fx_dir2 {AP : Type} (p : Formula AP) :
    [𝐅 (𝐗 p)] ⊢ [𝐗 (𝐅 p)] :=
  Derives.evL (𝐗 (𝐅 p)) (A := 𝐗 p) (by simp)
    (Derives.step (Γ' := [p]) (B := 𝐅 p)
      (Derives.evR (A := p) (by simp)
        (Derives.ax (A := p) (by simp) (by simp)))
      (by simp) (by simp))
    (Derives.step (Γ' := [𝐗 (𝐅 p)]) (B := 𝐅 p)
      (Derives.evR (A := p) (by simp)
        (Derives.ax (A := 𝐗 (𝐅 p)) (by simp) (by simp)))
      (by simp) (by simp))
    (Derives.ax (A := 𝐗 (𝐅 p)) (by simp) (by simp))

theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐗 (𝐅 (p))] ⊢ [𝐅 (𝐗 (p))]) ∧ ([𝐅 (𝐗 (p))] ⊢ [𝐗 (𝐅 (p))]) :=
  ⟨fx_dir1 p, fx_dir2 p⟩

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐗 (𝐅 (p))] ⊢ [𝐅 (𝐗 (p))]) ∧ ([𝐅 (𝐗 (p))] ⊢ [𝐗 (𝐅 (p))]) :=
  Candidate.candidate p

#print axioms verified
