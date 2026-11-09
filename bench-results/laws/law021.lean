import LTL

open LTL

-- LTL law 21: ⊥ U p ≈ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([(⊥ₗ 𝐔 p)] ⊢ [p]) ∧ ([p] ⊢ [(⊥ₗ 𝐔 p)]) :=
  ⟨.untilL (A := ⊥ₗ) (B := p) p (by simp)
      (.ax (A := p) (by simp) (by simp))
      (.botL (by simp))
      (.ax (A := p) (by simp) (by simp)),
   .untilR (A := ⊥ₗ) (B := p) (by simp)
      (.ax (A := p) (by simp) (by simp))
      (.ax (A := p) (by simp) (by simp))⟩

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(⊥ₗ 𝐔 p)] ⊢ [p]) ∧ ([p] ⊢ [(⊥ₗ 𝐔 p)]) :=
  Candidate.candidate p

#print axioms verified
