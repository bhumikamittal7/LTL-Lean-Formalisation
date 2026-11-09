import LTL

open LTL

-- LTL law 58: □ (◯ p ⇒ p) ⟹ (◇ p ⇒ p)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    [𝐆 ((𝐗 (p) ⇒ p))] ⊢ [(𝐅 (p) ⇒ p)] := by
  refine .impR (A := 𝐅 p) (B := p) (by simp) ?_
  refine Derives.evL (A := p) (I := 𝐆 (𝐗 p ⇒ p) ⇒ p) (by simp) ?_ ?_ ?_
  · exact .impR (A := 𝐆 (𝐗 p ⇒ p)) (B := p) (by simp)
      (.ax (A := p) (by simp) (by simp))
  · refine .impR (A := 𝐆 (𝐗 p ⇒ p)) (B := p) (by simp) ?_
    refine .alwaysL (A := 𝐗 p ⇒ p) (by simp) ?_
    refine .impL (A := 𝐗 p) (B := p) (by simp) ?_ (.ax (A := p) (by simp) (by simp))
    refine Derives.step (Γ' := [𝐆 (𝐗 p ⇒ p), 𝐆 (𝐗 p ⇒ p) ⇒ p]) (B := p) ?_
      (by simp) (by simp)
    exact .impL (A := 𝐆 (𝐗 p ⇒ p)) (B := p) (by simp)
      (.ax (A := 𝐆 (𝐗 p ⇒ p)) (by simp) (by simp))
      (.ax (A := p) (by simp) (by simp))
  · exact .impL (A := 𝐆 (𝐗 p ⇒ p)) (B := p) (by simp)
      (.ax (A := 𝐆 (𝐗 p ⇒ p)) (by simp) (by simp))
      (.ax (A := p) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    [𝐆 ((𝐗 (p) ⇒ p))] ⊢ [(𝐅 (p) ⇒ p)] :=
  Candidate.candidate p

#print axioms verified
