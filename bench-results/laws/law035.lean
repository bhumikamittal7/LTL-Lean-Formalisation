import LTL

open LTL

-- LTL law 35: (p U q) ∧ (p ∨ q) ≈ p U q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([((p 𝐔 q) ⋏ (p ⋎ q))] ⊢ [(p 𝐔 q)]) ∧ ([(p 𝐔 q)] ⊢ [((p 𝐔 q) ⋏ (p ⋎ q))]) :=
  ⟨Derives.andL (A := p 𝐔 q) (B := p ⋎ q) (by simp)
      (Derives.ax (A := p 𝐔 q) (by simp) (by simp)),
   Derives.andR (A := p 𝐔 q) (B := p ⋎ q) (by simp)
      (Derives.ax (A := p 𝐔 q) (by simp) (by simp))
      (Derives.untilL (A := p) (B := q) (I := p ⋎ q) (by simp)
        (Derives.orR (A := p) (B := q) (by simp)
          (Derives.ax (A := q) (by simp) (by simp)))
        (Derives.orR (A := p) (B := q) (by simp)
          (Derives.ax (A := p) (by simp) (by simp)))
        (Derives.ax (A := p ⋎ q) (by simp) (by simp)))⟩

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([((p 𝐔 q) ⋏ (p ⋎ q))] ⊢ [(p 𝐔 q)]) ∧ ([(p 𝐔 q)] ⊢ [((p 𝐔 q) ⋏ (p ⋎ q))]) :=
  Candidate.candidate p q

#print axioms verified
