import LTL

open LTL

-- LTL law 61: ¬◇ p ≈ □ ¬p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([∼(𝐅 (p))] ⊢ [𝐆 (∼(p))]) ∧ ([𝐆 (∼(p))] ⊢ [∼(𝐅 (p))]) := by
  refine ⟨?_, ?_⟩
  · exact
      Derives.alwaysR (A := ∼p) (I := ∼(𝐅 p)) (by simp)
        (Derives.ax (A := ∼(𝐅 p)) (by simp) (by simp))
        (Derives.negL (A := 𝐅 p) (by simp)
          (Derives.evR (A := p) (by simp)
            (Derives.next (Γ' := []) (Δ' := [𝐅 p, ∼(𝐅 p)])
              (Derives.negR (A := 𝐅 p) (by simp)
                (Derives.ax (A := 𝐅 p) (by simp) (by simp)))
              (by simp) (by simp))))
        (Derives.negR (A := p) (by simp)
          (Derives.negL (A := 𝐅 p) (by simp)
            (Derives.evR (A := p) (by simp)
              (Derives.ax (A := p) (by simp) (by simp)))))
  · exact
      Derives.negR (A := 𝐅 p) (by simp)
        (Derives.evL (A := p) (I := ∼(𝐆 (∼p))) (by simp)
          (Derives.negR (A := 𝐆 (∼p)) (by simp)
            (Derives.alwaysL (A := ∼p) (by simp)
              (Derives.negL (A := p) (by simp)
                (Derives.ax (A := p) (by simp) (by simp)))))
          (Derives.negR (A := 𝐆 (∼p)) (by simp)
            (Derives.alwaysL (A := ∼p) (by simp)
              (Derives.next (Γ' := [𝐆 (∼p), ∼(𝐆 (∼p))]) (Δ' := [])
                (Derives.negL (A := 𝐆 (∼p)) (by simp)
                  (Derives.ax (A := 𝐆 (∼p)) (by simp) (by simp)))
                (by simp) (by simp))))
          (Derives.negL (A := 𝐆 (∼p)) (by simp)
            (Derives.ax (A := 𝐆 (∼p)) (by simp) (by simp))))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([∼(𝐅 (p))] ⊢ [𝐆 (∼(p))]) ∧ ([𝐆 (∼(p))] ⊢ [∼(𝐅 (p))]) :=
  Candidate.candidate p

#print axioms verified
