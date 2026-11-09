import LTL

open LTL

-- LTL law 17: p U (q U r) ⟹ (p ∨ q) U r
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r : Formula AP) :
    [(p 𝐔 (q 𝐔 r))] ⊢ [((p ⋎ q) 𝐔 r)] := by
  have hr : [r] ⊢ [((p ⋎ q) 𝐔 r)] :=
    Derives.untilR (A := p ⋎ q) (B := r) (by simp)
      (Derives.ax (A := r) (by simp) (by simp))
      (Derives.ax (A := r) (by simp) (by simp))
  have hq : [q, 𝐗 ((p ⋎ q) 𝐔 r)] ⊢ [((p ⋎ q) 𝐔 r)] :=
    Derives.untilR (A := p ⋎ q) (B := r) (by simp)
      (Derives.orR (A := p) (B := q) (by simp)
        (Derives.ax (A := q) (by simp) (by simp)))
      (Derives.ax (A := 𝐗 ((p ⋎ q) 𝐔 r)) (by simp) (by simp))
  have hp : [p, 𝐗 ((p ⋎ q) 𝐔 r)] ⊢ [((p ⋎ q) 𝐔 r)] :=
    Derives.untilR (A := p ⋎ q) (B := r) (by simp)
      (Derives.orR (A := p) (B := q) (by simp)
        (Derives.ax (A := p) (by simp) (by simp)))
      (Derives.ax (A := 𝐗 ((p ⋎ q) 𝐔 r)) (by simp) (by simp))
  have hqr : [q 𝐔 r] ⊢ [((p ⋎ q) 𝐔 r)] :=
    Derives.untilL (A := q) (B := r) ((p ⋎ q) 𝐔 r) (by simp) hr hq
      (Derives.ax (A := (p ⋎ q) 𝐔 r) (by simp) (by simp))
  exact Derives.untilL (A := p) (B := q 𝐔 r) ((p ⋎ q) 𝐔 r) (by simp) hqr hp
    (Derives.ax (A := (p ⋎ q) 𝐔 r) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [(p 𝐔 (q 𝐔 r))] ⊢ [((p ⋎ q) 𝐔 r)] :=
  Candidate.candidate p q r

#print axioms verified
