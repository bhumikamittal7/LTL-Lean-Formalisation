import LTL

open LTL

-- LTL law 68: p ∧ □ p ≈ □ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([(p ⋏ 𝐆 (p))] ⊢ [𝐆 (p)]) ∧ ([𝐆 (p)] ⊢ [(p ⋏ 𝐆 (p))]) :=
  ⟨.andL (A := p) (B := 𝐆 p) (by simp) (.ax (A := 𝐆 p) (by simp) (by simp)),
   .andR (A := p) (B := 𝐆 p) (by simp)
     (.alwaysL (A := p) (by simp) (.ax (A := p) (by simp) (by simp)))
     (.ax (A := 𝐆 p) (by simp) (by simp))⟩

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(p ⋏ 𝐆 (p))] ⊢ [𝐆 (p)]) ∧ ([𝐆 (p)] ⊢ [(p ⋏ 𝐆 (p))]) :=
  Candidate.candidate p

#print axioms verified
