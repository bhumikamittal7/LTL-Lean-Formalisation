import LTL

open LTL

-- LTL law 110: □ p ⟹ (◇ q ⇒ ◇ (p ∨ q))
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐅 (q) ⇒ 𝐅 ((p ⋎ q)))] :=
  .impR (A := 𝐅 q) (B := 𝐅 (p ⋎ q)) (by simp)
    (.evR (A := p ⋎ q) (by simp)
      (.orR (A := p) (B := q) (by simp)
        (.alwaysL (A := p) (by simp)
          (.ax (A := p) (by simp) (by simp)))))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐅 (q) ⇒ 𝐅 ((p ⋎ q)))] :=
  Candidate.candidate p q

#print axioms verified
