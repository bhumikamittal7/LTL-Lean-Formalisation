import LTL

open LTL

-- LTL law 133: □ (p ⇒ ◇ q) ⟹ (◇ p ⇒ ◇ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ 𝐅 (q)))] ⊢ [(𝐅 (p) ⇒ 𝐅 (q))] :=
  .impR (A := 𝐅 p) (B := 𝐅 q) (by simp) <|
  .evL (A := p) ((𝐆 (p ⇒ 𝐅 q)) ⇒ (𝐅 q)) (by simp)
    (.impR (A := 𝐆 (p ⇒ 𝐅 q)) (B := 𝐅 q) (by simp) <|
      .alwaysL (A := p ⇒ 𝐅 q) (by simp) <|
      .impL (A := p) (B := 𝐅 q) (by simp)
        (.ax (A := p) (by simp) (by simp))
        (.ax (A := 𝐅 q) (by simp) (by simp)))
    (.impR (A := 𝐆 (p ⇒ 𝐅 q)) (B := 𝐅 q) (by simp) <|
      .alwaysL (A := p ⇒ 𝐅 q) (by simp) <|
      .evR (A := q) (by simp) <|
      Derives.step (Γ' := [(𝐆 (p ⇒ 𝐅 q)) ⇒ (𝐅 q), 𝐆 (p ⇒ 𝐅 q)]) (B := 𝐅 q)
        (.impL (A := 𝐆 (p ⇒ 𝐅 q)) (B := 𝐅 q) (by simp)
          (.ax (A := 𝐆 (p ⇒ 𝐅 q)) (by simp) (by simp))
          (.ax (A := 𝐅 q) (by simp) (by simp)))
        (by simp) (by simp))
    (.impL (A := 𝐆 (p ⇒ 𝐅 q)) (B := 𝐅 q) (by simp)
      (.ax (A := 𝐆 (p ⇒ 𝐅 q)) (by simp) (by simp))
      (.ax (A := 𝐅 q) (by simp) (by simp)))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ 𝐅 (q)))] ⊢ [(𝐅 (p) ⇒ 𝐅 (q))] :=
  Candidate.candidate p q

#print axioms verified
