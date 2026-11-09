import LTL

open LTL

-- LTL law 148: □ p ⟹ (◯ q ⇒ ◯ (p U q))
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐗 (q) ⇒ 𝐗 ((p 𝐔 q)))] := by
  exact Derives.impR (A := 𝐗 q) (B := 𝐗 (p 𝐔 q)) (by simp)
    (Derives.step (Γ' := [q]) (B := p 𝐔 q)
      (Derives.untilR (A := p) (B := q) (by simp)
        (.ax (A := q) (by simp) (by simp))
        (.ax (A := q) (by simp) (by simp)))
      (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐗 (q) ⇒ 𝐗 ((p 𝐔 q)))] :=
  Candidate.candidate p q

#print axioms verified
