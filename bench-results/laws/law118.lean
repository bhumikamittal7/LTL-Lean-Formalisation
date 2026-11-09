import LTL

open LTL

-- LTL law 118: □ (p ⇒ q) ⟹ (◯ p ⇒ ◯ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ q))] ⊢ [(𝐗 (p) ⇒ 𝐗 (q))] := by
  apply Derives.impR (A := 𝐗 p) (B := 𝐗 q) (by simp)
  apply Derives.alwaysL (A := p ⇒ q) (by simp)
  refine Derives.step (Γ' := [𝐆 (p ⇒ q), p]) (B := q) ?_ (by simp) (by simp)
  apply Derives.alwaysL (A := p ⇒ q) (by simp)
  apply Derives.impL (A := p) (B := q) (by simp)
  · exact .ax (A := p) (by simp) (by simp)
  · exact .ax (A := q) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ q))] ⊢ [(𝐗 (p) ⇒ 𝐗 (q))] :=
  Candidate.candidate p q

#print axioms verified
