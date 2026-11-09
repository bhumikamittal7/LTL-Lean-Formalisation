import LTL

open LTL

-- LTL law 98: ◇ □ p ∧ □ ◇ ¬p ≈ ⊥
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem helperX {AP : Type} (A : Formula AP) : [𝐗 (∼(𝐆 A))] ⊢ [∼(𝐆 A)] :=
  Derives.negR (A := 𝐆 A) (by simp)
    (Derives.alwaysL (A := A) (by simp)
      (Derives.next (Γ' := [∼(𝐆 A), 𝐆 A]) (Δ' := [])
        (Derives.negL (A := 𝐆 A) (by simp)
          (Derives.ax (A := 𝐆 A) (by simp) (by simp)))
        (by simp) (by simp)))

theorem helperBase {AP : Type} (p : Formula AP) : [𝐆 p] ⊢ [∼(𝐆 (𝐅 (∼p)))] :=
  Derives.negR (A := 𝐆 (𝐅 (∼p))) (by simp)
    (Derives.alwaysL (A := 𝐅 (∼p)) (by simp)
      (Derives.evL (A := ∼p) (I := ∼(𝐆 p)) (by simp)
        (Derives.negR (A := 𝐆 p) (by simp)
          (Derives.alwaysL (A := p) (by simp)
            (Derives.negL (A := p) (by simp)
              (Derives.ax (A := p) (by simp) (by simp)))))
        (helperX p)
        (Derives.negL (A := 𝐆 p) (by simp)
          (Derives.ax (A := 𝐆 p) (by simp) (by simp)))))

theorem candidate {AP : Type} (p : Formula AP) :
    ([(𝐅 (𝐆 (p)) ⋏ 𝐆 (𝐅 (∼(p))))] ⊢ [⊥ₗ]) ∧ ([⊥ₗ] ⊢ [(𝐅 (𝐆 (p)) ⋏ 𝐆 (𝐅 (∼(p))))]) :=
  ⟨Derives.andL (A := 𝐅 (𝐆 p)) (B := 𝐆 (𝐅 (∼p))) (by simp)
      (Derives.evL (A := 𝐆 p) (I := ∼(𝐆 (𝐅 (∼p)))) (by simp)
        (helperBase p)
        (helperX (𝐅 (∼p)))
        (Derives.negL (A := 𝐆 (𝐅 (∼p))) (by simp)
          (Derives.ax (A := 𝐆 (𝐅 (∼p))) (by simp) (by simp)))),
   Derives.botL (by simp)⟩

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(𝐅 (𝐆 (p)) ⋏ 𝐆 (𝐅 (∼(p))))] ⊢ [⊥ₗ]) ∧ ([⊥ₗ] ⊢ [(𝐅 (𝐆 (p)) ⋏ 𝐆 (𝐅 (∼(p))))]) :=
  Candidate.candidate p

#print axioms verified
