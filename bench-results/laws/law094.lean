import LTL

open LTL

-- LTL law 94: □ p ∧ □ ¬p ≈ ⊥
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([(𝐆 (p) ⋏ 𝐆 (∼(p)))] ⊢ [⊥ₗ]) ∧ ([⊥ₗ] ⊢ [(𝐆 (p) ⋏ 𝐆 (∼(p)))]) :=
  ⟨.andL (A := 𝐆 p) (B := 𝐆 (∼p)) (by simp)
     (.alwaysL (A := p) (by simp)
       (.alwaysL (A := ∼p) (by simp)
         (.negL (A := p) (by simp) (.ax (A := p) (by simp) (by simp))))),
   .botL (by simp)⟩

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(𝐆 (p) ⋏ 𝐆 (∼(p)))] ⊢ [⊥ₗ]) ∧ ([⊥ₗ] ⊢ [(𝐆 (p) ⋏ 𝐆 (∼(p)))]) :=
  Candidate.candidate p

#print axioms verified
