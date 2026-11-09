import LTL

open LTL

-- LTL law 134: □ (p ⇒ ◯ q) ⟹ (p ⇒ ◇ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ 𝐗 (q)))] ⊢ [(p ⇒ 𝐅 (q))] := by
  apply Derives.impR (A := p) (B := 𝐅 (q)) (by simp)
  apply Derives.alwaysL (A := (p ⇒ 𝐗 (q))) (by simp)
  apply Derives.evR (A := q) (by simp)
  apply Derives.impL (A := p) (B := 𝐗 (q)) (by simp)
  · exact .ax (A := p) (by simp) (by simp)
  · apply Derives.step (Γ' := [q]) (B := 𝐅 (q))
    · apply Derives.evR (A := q) (by simp)
      exact .ax (A := q) (by simp) (by simp)
    · simp
    · simp

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ 𝐗 (q)))] ⊢ [(p ⇒ 𝐅 (q))] :=
  Candidate.candidate p q

#print axioms verified
