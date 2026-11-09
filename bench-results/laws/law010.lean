import LTL

open LTL

-- LTL law 10: p U q ≈ q ∨ (p ∧ ◯ (p U q))
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem dir2 {AP : Type} (p q : Formula AP) :
    [(q ⋎ (p ⋏ 𝐗 ((p 𝐔 q))))] ⊢ [(p 𝐔 q)] :=
  Derives.orL (A := q) (B := p ⋏ 𝐗 (p 𝐔 q)) (by simp)
    (Derives.untilR (A := p) (B := q) (by simp)
      (.ax (A := q) (by simp) (by simp))
      (.ax (A := q) (by simp) (by simp)))
    (Derives.andL (A := p) (B := 𝐗 (p 𝐔 q)) (by simp)
      (Derives.untilR (A := p) (B := q) (by simp)
        (.ax (A := p) (by simp) (by simp))
        (.ax (A := 𝐗 (p 𝐔 q)) (by simp) (by simp))))

theorem dir1 {AP : Type} (p q : Formula AP) :
    [(p 𝐔 q)] ⊢ [(q ⋎ (p ⋏ 𝐗 ((p 𝐔 q))))] :=
  Derives.untilL (q ⋎ (p ⋏ 𝐗 (p 𝐔 q))) (A := p) (B := q) (by simp)
    (Derives.orR (A := q) (B := p ⋏ 𝐗 (p 𝐔 q)) (by simp)
      (.ax (A := q) (by simp) (by simp)))
    (Derives.orR (A := q) (B := p ⋏ 𝐗 (p 𝐔 q)) (by simp)
      (Derives.andR (A := p) (B := 𝐗 (p 𝐔 q)) (by simp)
        (.ax (A := p) (by simp) (by simp))
        (Derives.step (Γ' := [q ⋎ (p ⋏ 𝐗 (p 𝐔 q))]) (B := p 𝐔 q)
          (dir2 p q) (by simp) (by simp))))
    (.ax (A := q ⋎ (p ⋏ 𝐗 (p 𝐔 q))) (by simp) (by simp))

theorem candidate {AP : Type} (p q : Formula AP) :
    ([(p 𝐔 q)] ⊢ [(q ⋎ (p ⋏ 𝐗 ((p 𝐔 q))))]) ∧ ([(q ⋎ (p ⋏ 𝐗 ((p 𝐔 q))))] ⊢ [(p 𝐔 q)]) :=
  ⟨dir1 p q, dir2 p q⟩

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([(p 𝐔 q)] ⊢ [(q ⋎ (p ⋏ 𝐗 ((p 𝐔 q))))]) ∧ ([(q ⋎ (p ⋏ 𝐗 ((p 𝐔 q))))] ⊢ [(p 𝐔 q)]) :=
  Candidate.candidate p q

#print axioms verified
