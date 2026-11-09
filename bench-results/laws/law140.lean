import LTL

open LTL

-- LTL law 140: p U □ q ⟹ □ (p U q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [(p 𝐔 𝐆 (q))] ⊢ [𝐆 ((p 𝐔 q))] := by
  have hJ : [((𝐗 (p 𝐔 (𝐆 q))) ⋏ (p 𝐔 (𝐆 q)))] ⊢ [p 𝐔 (𝐆 q)] :=
    Derives.andL (A := 𝐗 (p 𝐔 (𝐆 q))) (B := p 𝐔 (𝐆 q)) (by simp)
      (.ax (A := p 𝐔 (𝐆 q)) (by simp) (by simp))
  have hG : [𝐆 q] ⊢ [p 𝐔 (𝐆 q)] :=
    Derives.untilR (A := p) (B := 𝐆 q) (by simp)
      (.ax (A := 𝐆 q) (by simp) (by simp))
      (.ax (A := 𝐆 q) (by simp) (by simp))
  apply Derives.alwaysR (A := p 𝐔 q) (I := p 𝐔 (𝐆 q)) (by simp)
  · exact .ax (A := p 𝐔 (𝐆 q)) (by simp) (by simp)
  · exact Derives.untilL (A := p) (B := 𝐆 q)
      (I := ((𝐗 (p 𝐔 (𝐆 q))) ⋏ (p 𝐔 (𝐆 q)))) (by simp)
      (Derives.andR (A := 𝐗 (p 𝐔 (𝐆 q))) (B := p 𝐔 (𝐆 q)) (by simp)
        (Derives.alwaysL (A := q) (by simp)
          (Derives.step (Γ' := [𝐆 q]) (B := p 𝐔 (𝐆 q)) hG (by simp) (by simp)))
        (Derives.untilR (A := p) (B := 𝐆 q) (by simp)
          (.ax (A := 𝐆 q) (by simp) (by simp))
          (.ax (A := 𝐆 q) (by simp) (by simp))))
      (Derives.andR (A := 𝐗 (p 𝐔 (𝐆 q))) (B := p 𝐔 (𝐆 q)) (by simp)
        (Derives.step (Γ' := [((𝐗 (p 𝐔 (𝐆 q))) ⋏ (p 𝐔 (𝐆 q)))])
          (B := p 𝐔 (𝐆 q)) hJ (by simp) (by simp))
        (Derives.untilR (A := p) (B := 𝐆 q) (by simp)
          (.ax (A := p) (by simp) (by simp))
          (Derives.step (Γ' := [((𝐗 (p 𝐔 (𝐆 q))) ⋏ (p 𝐔 (𝐆 q)))])
            (B := p 𝐔 (𝐆 q)) hJ (by simp) (by simp))))
      (Derives.andL (A := 𝐗 (p 𝐔 (𝐆 q))) (B := p 𝐔 (𝐆 q)) (by simp)
        (.ax (A := 𝐗 (p 𝐔 (𝐆 q))) (by simp) (by simp)))
  · exact Derives.untilL (A := p) (B := 𝐆 q) (I := p 𝐔 q) (by simp)
      (Derives.alwaysL (A := q) (by simp)
        (Derives.untilR (A := p) (B := q) (by simp)
          (.ax (A := q) (by simp) (by simp))
          (.ax (A := q) (by simp) (by simp))))
      (Derives.untilR (A := p) (B := q) (by simp)
        (.ax (A := p) (by simp) (by simp))
        (.ax (A := 𝐗 (p 𝐔 q)) (by simp) (by simp)))
      (.ax (A := p 𝐔 q) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [(p 𝐔 𝐆 (q))] ⊢ [𝐆 ((p 𝐔 q))] :=
  Candidate.candidate p q

#print axioms verified
