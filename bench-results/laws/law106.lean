import LTL

open LTL

-- LTL law 106: □ p ⟹ (◯ q ⇒ ◯ (p ∧ q))
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐗 (q) ⇒ 𝐗 ((p ⋏ q)))] :=
  .impR (A := 𝐗 (q)) (B := 𝐗 ((p ⋏ q))) (by simp)
    (.alwaysL (A := p) (by simp)
      (Derives.step (Γ' := [𝐆 (p), q]) (B := (p ⋏ q))
        (.andR (A := p) (B := q) (by simp)
          (.alwaysL (A := p) (by simp) (.ax (A := p) (by simp) (by simp)))
          (.ax (A := q) (by simp) (by simp)))
        (by simp) (by simp)))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐗 (q) ⇒ 𝐗 ((p ⋏ q)))] :=
  Candidate.candidate p q

#print axioms verified
