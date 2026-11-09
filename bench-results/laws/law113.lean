import LTL

open LTL

-- LTL law 113: □ p ⟹ (◇ q ⇒ ◇ (p ⇒ q))
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐅 (q) ⇒ 𝐅 ((p ⇒ q)))] :=
  .impR (A := 𝐅 q) (B := 𝐅 (p ⇒ q)) (by simp)
    (.evL (A := q) (I := 𝐅 (p ⇒ q)) (by simp)
      (.evR (A := p ⇒ q) (by simp)
        (.impR (A := p) (B := q) (by simp) (.ax (A := q) (by simp) (by simp))))
      (.evR (A := p ⇒ q) (by simp)
        (.ax (A := 𝐗 (𝐅 (p ⇒ q))) (by simp) (by simp)))
      (.ax (A := 𝐅 (p ⇒ q)) (by simp) (by simp)))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐅 (q) ⇒ 𝐅 ((p ⇒ q)))] :=
  Candidate.candidate p q

#print axioms verified
