import LTL

open LTL

-- LTL law 5: ◯ (p ∧ q) ≈ ◯ p ∧ ◯ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([𝐗 ((p ⋏ q))] ⊢ [(𝐗 (p) ⋏ 𝐗 (q))]) ∧ ([(𝐗 (p) ⋏ 𝐗 (q))] ⊢ [𝐗 ((p ⋏ q))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.andR (A := 𝐗 p) (B := 𝐗 q) (by simp)
      (Derives.step (Γ' := [p ⋏ q]) (B := p)
        (Derives.andL (A := p) (B := q) (by simp)
          (Derives.ax (A := p) (by simp) (by simp)))
        (by simp) (by simp))
      (Derives.step (Γ' := [p ⋏ q]) (B := q)
        (Derives.andL (A := p) (B := q) (by simp)
          (Derives.ax (A := q) (by simp) (by simp)))
        (by simp) (by simp))
  · exact Derives.andL (A := 𝐗 p) (B := 𝐗 q) (by simp)
      (Derives.step (Γ' := [p, q]) (B := p ⋏ q)
        (Derives.andR (A := p) (B := q) (by simp)
          (Derives.ax (A := p) (by simp) (by simp))
          (Derives.ax (A := q) (by simp) (by simp)))
        (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([𝐗 ((p ⋏ q))] ⊢ [(𝐗 (p) ⋏ 𝐗 (q))]) ∧ ([(𝐗 (p) ⋏ 𝐗 (q))] ⊢ [𝐗 ((p ⋏ q))]) :=
  Candidate.candidate p q

#print axioms verified
