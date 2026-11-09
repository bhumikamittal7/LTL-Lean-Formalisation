import LTL

open LTL

-- LTL law 18: p U (q ∧ r) ⟹ (p U q) U r
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r : Formula AP) :
    [(p 𝐔 (q ⋏ r))] ⊢ [((p 𝐔 q) 𝐔 r)] := by
  have hU : [((p 𝐔 q) 𝐔 r) ⋏ (p 𝐔 q)] ⊢ [((p 𝐔 q) 𝐔 r)] :=
    .andL (A := (p 𝐔 q) 𝐔 r) (B := p 𝐔 q) (by simp)
      (.ax (A := (p 𝐔 q) 𝐔 r) (by simp) (by simp))
  have hP : [((p 𝐔 q) 𝐔 r) ⋏ (p 𝐔 q)] ⊢ [(p 𝐔 q)] :=
    .andL (A := (p 𝐔 q) 𝐔 r) (B := p 𝐔 q) (by simp)
      (.ax (A := p 𝐔 q) (by simp) (by simp))
  have base : [q ⋏ r] ⊢ [((p 𝐔 q) 𝐔 r) ⋏ (p 𝐔 q)] :=
    .andL (A := q) (B := r) (by simp)
      (.andR (A := (p 𝐔 q) 𝐔 r) (B := p 𝐔 q) (by simp)
        (.untilR (A := p 𝐔 q) (B := r) (by simp)
          (.ax (A := r) (by simp) (by simp))
          (.ax (A := r) (by simp) (by simp)))
        (.untilR (A := p) (B := q) (by simp)
          (.ax (A := q) (by simp) (by simp))
          (.ax (A := q) (by simp) (by simp))))
  have stp : [p, 𝐗 (((p 𝐔 q) 𝐔 r) ⋏ (p 𝐔 q))] ⊢ [((p 𝐔 q) 𝐔 r) ⋏ (p 𝐔 q)] :=
    .andR (A := (p 𝐔 q) 𝐔 r) (B := p 𝐔 q) (by simp)
      (.untilR (A := p 𝐔 q) (B := r) (by simp)
        (.untilR (A := p) (B := q) (by simp)
          (.ax (A := p) (by simp) (by simp))
          (.step (Γ' := [((p 𝐔 q) 𝐔 r) ⋏ (p 𝐔 q)]) hP (by simp) (by simp)))
        (.step (Γ' := [((p 𝐔 q) 𝐔 r) ⋏ (p 𝐔 q)]) hU (by simp) (by simp)))
      (.untilR (A := p) (B := q) (by simp)
        (.ax (A := p) (by simp) (by simp))
        (.step (Γ' := [((p 𝐔 q) 𝐔 r) ⋏ (p 𝐔 q)]) hP (by simp) (by simp)))
  exact .untilL (A := p) (B := q ⋏ r) (((p 𝐔 q) 𝐔 r) ⋏ (p 𝐔 q)) (by simp) base stp
    (.andL (A := (p 𝐔 q) 𝐔 r) (B := p 𝐔 q) (by simp)
      (.ax (A := (p 𝐔 q) 𝐔 r) (by simp) (by simp)))

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [(p 𝐔 (q ⋏ r))] ⊢ [((p 𝐔 q) 𝐔 r)] :=
  Candidate.candidate p q r

#print axioms verified
