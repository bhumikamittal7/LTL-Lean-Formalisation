import LTL

open LTL

-- LTL law 13: (p U r) ∨ (q U r) ⟹ (p ∨ q) U r
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r : Formula AP) :
    [((p 𝐔 r) ⋎ (q 𝐔 r))] ⊢ [((p ⋎ q) 𝐔 r)] := by
  apply Derives.orL (A := p 𝐔 r) (B := q 𝐔 r) (by simp)
  · apply Derives.untilL (A := p) (B := r) (I := (p ⋎ q) 𝐔 r) (by simp)
    · exact Derives.untilR (A := p ⋎ q) (B := r) (by simp)
        (.ax (A := r) (by simp) (by simp))
        (.ax (A := r) (by simp) (by simp))
    · exact Derives.untilR (A := p ⋎ q) (B := r) (by simp)
        (Derives.orR (A := p) (B := q) (by simp) (.ax (A := p) (by simp) (by simp)))
        (.ax (A := 𝐗 ((p ⋎ q) 𝐔 r)) (by simp) (by simp))
    · exact .ax (A := (p ⋎ q) 𝐔 r) (by simp) (by simp)
  · apply Derives.untilL (A := q) (B := r) (I := (p ⋎ q) 𝐔 r) (by simp)
    · exact Derives.untilR (A := p ⋎ q) (B := r) (by simp)
        (.ax (A := r) (by simp) (by simp))
        (.ax (A := r) (by simp) (by simp))
    · exact Derives.untilR (A := p ⋎ q) (B := r) (by simp)
        (Derives.orR (A := p) (B := q) (by simp) (.ax (A := q) (by simp) (by simp)))
        (.ax (A := 𝐗 ((p ⋎ q) 𝐔 r)) (by simp) (by simp))
    · exact .ax (A := (p ⋎ q) 𝐔 r) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [((p 𝐔 r) ⋎ (q 𝐔 r))] ⊢ [((p ⋎ q) 𝐔 r)] :=
  Candidate.candidate p q r

#print axioms verified
