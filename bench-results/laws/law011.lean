import LTL

open LTL

-- LTL law 11: p U ⊥ ⟹ ⊥
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    [(p 𝐔 ⊥ₗ)] ⊢ [⊥ₗ] :=
  Derives.untilL (A := p) (B := ⊥ₗ) ⊥ₗ (by simp)
    (Derives.botL (by simp))
    (Derives.next (Γ' := [⊥ₗ]) (Δ' := ([] : List (Formula AP)))
      (Derives.botL (by simp)) (by simp) (by simp))
    (Derives.botL (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    [(p 𝐔 ⊥ₗ)] ⊢ [⊥ₗ] :=
  Candidate.candidate p

#print axioms verified
