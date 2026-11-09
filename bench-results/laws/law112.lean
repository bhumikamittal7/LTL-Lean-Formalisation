import LTL

open LTL

-- LTL law 112: □ p ⟹ (◯ q ⇒ ◯ (p ⇒ q))
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐗 (q) ⇒ 𝐗 ((p ⇒ q)))] :=
  Derives.impR (A := 𝐗 q) (B := 𝐗 (p ⇒ q)) (by simp)
    (Derives.step (Γ' := [q]) (B := p ⇒ q)
      (Derives.impR (A := p) (B := q) (by simp)
        (Derives.ax (A := q) (by simp) (by simp)))
      (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐗 (q) ⇒ 𝐗 ((p ⇒ q)))] :=
  Candidate.candidate p q

#print axioms verified
