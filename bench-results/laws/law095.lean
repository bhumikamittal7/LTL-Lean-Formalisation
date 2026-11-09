import LTL

open LTL

-- LTL law 95: □ ◇ p ∨ ◇ □ ¬p ≈ ⊤
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem hlpNext {AP : Type} (q : Formula AP) :
    [∼(𝐅 q)] ⊢ [𝐗 (∼(𝐅 q))] :=
  Derives.negL (A := 𝐅 q) (by simp)
    (Derives.evR (A := q) (by simp)
      (Derives.next (Γ' := []) (Δ' := [𝐅 q, ∼(𝐅 q)])
        (Derives.negR (A := 𝐅 q) (by simp)
          (Derives.ax (A := 𝐅 q) (by simp) (by simp)))
        (by simp) (by simp)))

theorem hlpNegP {AP : Type} (p : Formula AP) :
    [∼(𝐅 p)] ⊢ [∼p] :=
  Derives.negR (A := p) (by simp)
    (Derives.negL (A := 𝐅 p) (by simp)
      (Derives.evR (A := p) (by simp)
        (Derives.ax (A := p) (by simp) (by simp))))

theorem hlpEv {AP : Type} (p : Formula AP) :
    [∼(𝐅 (𝐆 (∼p)))] ⊢ [𝐅 p] :=
  Derives.negL (A := 𝐅 (𝐆 (∼p))) (by simp)
    (Derives.evR (A := 𝐆 (∼p)) (by simp)
      (Derives.alwaysR (A := ∼p) (I := ∼(𝐅 p)) (by simp)
        (Derives.negR (A := 𝐅 p) (by simp)
          (Derives.ax (A := 𝐅 p) (by simp) (by simp)))
        (hlpNext p)
        (hlpNegP p)))

theorem candidate {AP : Type} (p : Formula AP) :
    ([(𝐆 (𝐅 (p)) ⋎ 𝐅 (𝐆 (∼(p))))] ⊢ [⊤ₗ]) ∧ ([⊤ₗ] ⊢ [(𝐆 (𝐅 (p)) ⋎ 𝐅 (𝐆 (∼(p))))]) :=
  ⟨Derives.topR (by simp),
   Derives.orR (A := 𝐆 (𝐅 p)) (B := 𝐅 (𝐆 (∼p))) (by simp)
    (Derives.alwaysR (A := 𝐅 p) (I := ∼(𝐅 (𝐆 (∼p)))) (by simp)
      (Derives.negR (A := 𝐅 (𝐆 (∼p))) (by simp)
        (Derives.ax (A := 𝐅 (𝐆 (∼p))) (by simp) (by simp)))
      (hlpNext (𝐆 (∼p)))
      (hlpEv p))⟩

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(𝐆 (𝐅 (p)) ⋎ 𝐅 (𝐆 (∼(p))))] ⊢ [⊤ₗ]) ∧ ([⊤ₗ] ⊢ [(𝐆 (𝐅 (p)) ⋎ 𝐅 (𝐆 (∼(p))))]) :=
  Candidate.candidate p

#print axioms verified
