import LTL

open LTL

-- LTL law 4: ◯ (p ∨ q) ≈ ◯ p ∨ ◯ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([𝐗 ((p ⋎ q))] ⊢ [(𝐗 (p) ⋎ 𝐗 (q))]) ∧ ([(𝐗 (p) ⋎ 𝐗 (q))] ⊢ [𝐗 ((p ⋎ q))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.orR (A := 𝐗 p) (B := 𝐗 q) (by simp)
      (Derives.next (Γ' := [p ⋎ q]) (Δ' := [p, q])
        (Derives.orL (A := p) (B := q) (by simp)
          (Derives.ax (A := p) (by simp) (by simp))
          (Derives.ax (A := q) (by simp) (by simp)))
        (by simp) (by simp))
  · exact Derives.orL (A := 𝐗 p) (B := 𝐗 q) (by simp)
      (Derives.step (Γ' := [p]) (B := p ⋎ q)
        (Derives.orR (A := p) (B := q) (by simp)
          (Derives.ax (A := p) (by simp) (by simp)))
        (by simp) (by simp))
      (Derives.step (Γ' := [q]) (B := p ⋎ q)
        (Derives.orR (A := p) (B := q) (by simp)
          (Derives.ax (A := q) (by simp) (by simp)))
        (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([𝐗 ((p ⋎ q))] ⊢ [(𝐗 (p) ⋎ 𝐗 (q))]) ∧ ([(𝐗 (p) ⋎ 𝐗 (q))] ⊢ [𝐗 ((p ⋎ q))]) :=
  Candidate.candidate p q

#print axioms verified
