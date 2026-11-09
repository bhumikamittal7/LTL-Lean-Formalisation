import LTL

open LTL

-- LTL law 14: p U (q ∧ r) ⟹ (p U q) ∧ (p U r)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem untilAndLeft {AP : Type} (p q r : Formula AP) :
    [(p 𝐔 (q ⋏ r))] ⊢ [(p 𝐔 q)] :=
  Derives.untilL (A := p) (B := (q ⋏ r)) (I := (p 𝐔 q)) (by simp)
    (Derives.untilR (A := p) (B := q) (by simp)
      (Derives.andL (A := q) (B := r) (by simp)
        (Derives.ax (A := q) (by simp) (by simp)))
      (Derives.andL (A := q) (B := r) (by simp)
        (Derives.ax (A := q) (by simp) (by simp))))
    (Derives.untilR (A := p) (B := q) (by simp)
      (Derives.ax (A := p) (by simp) (by simp))
      (Derives.ax (A := 𝐗 (p 𝐔 q)) (by simp) (by simp)))
    (Derives.ax (A := (p 𝐔 q)) (by simp) (by simp))

theorem untilAndRight {AP : Type} (p q r : Formula AP) :
    [(p 𝐔 (q ⋏ r))] ⊢ [(p 𝐔 r)] :=
  Derives.untilL (A := p) (B := (q ⋏ r)) (I := (p 𝐔 r)) (by simp)
    (Derives.untilR (A := p) (B := r) (by simp)
      (Derives.andL (A := q) (B := r) (by simp)
        (Derives.ax (A := r) (by simp) (by simp)))
      (Derives.andL (A := q) (B := r) (by simp)
        (Derives.ax (A := r) (by simp) (by simp))))
    (Derives.untilR (A := p) (B := r) (by simp)
      (Derives.ax (A := p) (by simp) (by simp))
      (Derives.ax (A := 𝐗 (p 𝐔 r)) (by simp) (by simp)))
    (Derives.ax (A := (p 𝐔 r)) (by simp) (by simp))

theorem candidate {AP : Type} (p q r : Formula AP) :
    [(p 𝐔 (q ⋏ r))] ⊢ [((p 𝐔 q) ⋏ (p 𝐔 r))] :=
  Derives.andR (A := (p 𝐔 q)) (B := (p 𝐔 r)) (by simp)
    (Derives.wk (untilAndLeft p q r) (by simp) (by simp))
    (Derives.wk (untilAndRight p q r) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [(p 𝐔 (q ⋏ r))] ⊢ [((p 𝐔 q) ⋏ (p 𝐔 r))] :=
  Candidate.candidate p q r

#print axioms verified
