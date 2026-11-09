import LTL

open LTL

-- LTL law 74: p ⇒ □ p ⟹ p ⇒ ◯ □ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    [(p ⇒ 𝐆 (p))] ⊢ [(p ⇒ 𝐗 (𝐆 (p)))] :=
  .impR (A := p) (B := 𝐗 (𝐆 p)) (by simp)
    (.impL (A := p) (B := 𝐆 p) (by simp)
      (.ax (A := p) (by simp) (by simp))
      (.alwaysL (A := p) (by simp)
        (.ax (A := 𝐗 (𝐆 p)) (by simp) (by simp))))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    [(p ⇒ 𝐆 (p))] ⊢ [(p ⇒ 𝐗 (𝐆 (p)))] :=
  Candidate.candidate p

#print axioms verified
