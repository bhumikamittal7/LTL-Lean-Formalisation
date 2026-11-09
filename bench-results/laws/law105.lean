import LTL

open LTL

-- LTL law 105: (◇ p ⇒ ◇ q) ⟹ ◇ (p ⇒ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [(𝐅 (p) ⇒ 𝐅 (q))] ⊢ [𝐅 ((p ⇒ q))] :=
  Derives.impL (A := 𝐅 p) (B := 𝐅 q) (by simp)
    (Derives.evR (A := p ⇒ q) (by simp)
      (Derives.impR (A := p) (B := q) (by simp)
        (Derives.evR (A := p) (by simp)
          (Derives.ax (A := p) (by simp) (by simp)))))
    (Derives.evL (A := q) (I := 𝐅 (p ⇒ q)) (by simp)
      (Derives.evR (A := p ⇒ q) (by simp)
        (Derives.impR (A := p) (B := q) (by simp)
          (Derives.ax (A := q) (by simp) (by simp))))
      (Derives.evR (A := p ⇒ q) (by simp)
        (Derives.ax (A := 𝐗 (𝐅 (p ⇒ q))) (by simp) (by simp)))
      (Derives.ax (A := 𝐅 (p ⇒ q)) (by simp) (by simp)))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [(𝐅 (p) ⇒ 𝐅 (q))] ⊢ [𝐅 ((p ⇒ q))] :=
  Candidate.candidate p q

#print axioms verified
