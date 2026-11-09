import LTL

open LTL

-- LTL law 194: ◇ p ⟹ (p ⇒ q) U p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐅 (p)] ⊢ [((p ⇒ q) 𝐔 p)] :=
  Derives.evL (A := p) (I := (p ⇒ q) 𝐔 p) (by simp)
    (Derives.untilR (A := p ⇒ q) (B := p) (by simp)
      (Derives.ax (A := p) (by simp) (by simp))
      (Derives.ax (A := p) (by simp) (by simp)))
    (Derives.untilR (A := p ⇒ q) (B := p) (by simp)
      (Derives.impR (A := p) (B := q) (by simp)
        (Derives.ax (A := p) (by simp) (by simp)))
      (Derives.ax (A := 𝐗 ((p ⇒ q) 𝐔 p)) (by simp) (by simp)))
    (Derives.ax (A := (p ⇒ q) 𝐔 p) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐅 (p)] ⊢ [((p ⇒ q) 𝐔 p)] :=
  Candidate.candidate p q

#print axioms verified
