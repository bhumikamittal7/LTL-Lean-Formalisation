import LTL

open LTL

-- LTL law 53: ◇ (p ∧ q) ⟹ ◇ p ∧ ◇ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐅 ((p ⋏ q))] ⊢ [(𝐅 (p) ⋏ 𝐅 (q))] :=
  Derives.andR (A := 𝐅 p) (B := 𝐅 q) (by simp)
    (Derives.evL (A := p ⋏ q) (I := 𝐅 p) (by simp)
      (Derives.andL (A := p) (B := q) (by simp)
        (Derives.evR (A := p) (by simp)
          (Derives.ax (A := p) (by simp) (by simp))))
      (Derives.evR (A := p) (by simp)
        (Derives.ax (A := 𝐗 (𝐅 p)) (by simp) (by simp)))
      (Derives.ax (A := 𝐅 p) (by simp) (by simp)))
    (Derives.evL (A := p ⋏ q) (I := 𝐅 q) (by simp)
      (Derives.andL (A := p) (B := q) (by simp)
        (Derives.evR (A := q) (by simp)
          (Derives.ax (A := q) (by simp) (by simp))))
      (Derives.evR (A := q) (by simp)
        (Derives.ax (A := 𝐗 (𝐅 q)) (by simp) (by simp)))
      (Derives.ax (A := 𝐅 q) (by simp) (by simp)))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐅 ((p ⋏ q))] ⊢ [(𝐅 (p) ⋏ 𝐅 (q))] :=
  Candidate.candidate p q

#print axioms verified
