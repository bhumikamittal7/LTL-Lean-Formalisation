import LTL

open LTL

-- LTL law 52: ◇ (p ∨ q) ≈ ◇ p ∨ ◇ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([𝐅 ((p ⋎ q))] ⊢ [(𝐅 (p) ⋎ 𝐅 (q))]) ∧ ([(𝐅 (p) ⋎ 𝐅 (q))] ⊢ [𝐅 ((p ⋎ q))]) := by
  constructor
  · exact Derives.evL (A := p ⋎ q) (I := 𝐅 p ⋎ 𝐅 q) (by simp)
      (Derives.orR (A := 𝐅 p) (B := 𝐅 q) (by simp)
        (Derives.orL (A := p) (B := q) (by simp)
          (Derives.evR (A := p) (by simp) (.ax (A := p) (by simp) (by simp)))
          (Derives.evR (A := q) (by simp) (.ax (A := q) (by simp) (by simp)))))
      (Derives.orR (A := 𝐅 p) (B := 𝐅 q) (by simp)
        (Derives.evR (A := p) (by simp)
          (Derives.evR (A := q) (by simp)
            (Derives.next (Γ' := [𝐅 p ⋎ 𝐅 q]) (Δ' := [𝐅 p, 𝐅 q])
              (Derives.orL (A := 𝐅 p) (B := 𝐅 q) (by simp)
                (.ax (A := 𝐅 p) (by simp) (by simp))
                (.ax (A := 𝐅 q) (by simp) (by simp)))
              (by simp) (by simp)))))
      (.ax (A := 𝐅 p ⋎ 𝐅 q) (by simp) (by simp))
  · exact Derives.orL (A := 𝐅 p) (B := 𝐅 q) (by simp)
      (Derives.evL (A := p) (I := 𝐅 (p ⋎ q)) (by simp)
        (Derives.evR (A := p ⋎ q) (by simp)
          (Derives.orR (A := p) (B := q) (by simp)
            (.ax (A := p) (by simp) (by simp))))
        (Derives.evR (A := p ⋎ q) (by simp)
          (.ax (A := 𝐗 (𝐅 (p ⋎ q))) (by simp) (by simp)))
        (.ax (A := 𝐅 (p ⋎ q)) (by simp) (by simp)))
      (Derives.evL (A := q) (I := 𝐅 (p ⋎ q)) (by simp)
        (Derives.evR (A := p ⋎ q) (by simp)
          (Derives.orR (A := p) (B := q) (by simp)
            (.ax (A := q) (by simp) (by simp))))
        (Derives.evR (A := p ⋎ q) (by simp)
          (.ax (A := 𝐗 (𝐅 (p ⋎ q))) (by simp) (by simp)))
        (.ax (A := 𝐅 (p ⋎ q)) (by simp) (by simp)))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([𝐅 ((p ⋎ q))] ⊢ [(𝐅 (p) ⋎ 𝐅 (q))]) ∧ ([(𝐅 (p) ⋎ 𝐅 (q))] ⊢ [𝐅 ((p ⋎ q))]) :=
  Candidate.candidate p q

#print axioms verified
