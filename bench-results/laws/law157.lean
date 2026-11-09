import LTL

open LTL

-- LTL law 157: □ (p ⇒ q) ⟹ (□ ◇ p ⇒ □ ◇ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ q))] ⊢ [(𝐆 (𝐅 (p)) ⇒ 𝐆 (𝐅 (q)))] := by
  refine .impR (A := 𝐆 (𝐅 p)) (B := 𝐆 (𝐅 q)) (by simp) ?_
  refine .alwaysR (A := 𝐅 q) (𝐆 (p ⇒ q) ⋏ 𝐆 (𝐅 p)) (by simp) ?_ ?_ ?_
  · exact .andR (A := 𝐆 (p ⇒ q)) (B := 𝐆 (𝐅 p)) (by simp)
      (.ax (A := 𝐆 (p ⇒ q)) (by simp) (by simp))
      (.ax (A := 𝐆 (𝐅 p)) (by simp) (by simp))
  · refine .andL (A := 𝐆 (p ⇒ q)) (B := 𝐆 (𝐅 p)) (by simp) ?_
    refine .alwaysL (A := p ⇒ q) (by simp) ?_
    refine .alwaysL (A := 𝐅 p) (by simp) ?_
    refine Derives.step (Γ' := [𝐆 (p ⇒ q), 𝐆 (𝐅 p)])
      (?_ : [𝐆 (p ⇒ q), 𝐆 (𝐅 p)] ⊢ [𝐆 (p ⇒ q) ⋏ 𝐆 (𝐅 p)]) (by simp) (by simp)
    exact .andR (A := 𝐆 (p ⇒ q)) (B := 𝐆 (𝐅 p)) (by simp)
      (.ax (A := 𝐆 (p ⇒ q)) (by simp) (by simp))
      (.ax (A := 𝐆 (𝐅 p)) (by simp) (by simp))
  · refine .andL (A := 𝐆 (p ⇒ q)) (B := 𝐆 (𝐅 p)) (by simp) ?_
    refine .alwaysL (A := 𝐅 p) (by simp) ?_
    refine Derives.evL (A := p) (𝐆 (p ⇒ q) ⇒ 𝐅 q) (by simp) ?_ ?_ ?_
    · refine .impR (A := 𝐆 (p ⇒ q)) (B := 𝐅 q) (by simp) ?_
      refine .alwaysL (A := p ⇒ q) (by simp) ?_
      refine .impL (A := p) (B := q) (by simp) (.ax (A := p) (by simp) (by simp)) ?_
      exact Derives.evR (A := q) (by simp) (.ax (A := q) (by simp) (by simp))
    · refine .impR (A := 𝐆 (p ⇒ q)) (B := 𝐅 q) (by simp) ?_
      refine .alwaysL (A := p ⇒ q) (by simp) ?_
      refine Derives.evR (A := q) (by simp) ?_
      refine .next (?_ : [𝐆 (p ⇒ q) ⇒ 𝐅 q, 𝐆 (p ⇒ q)] ⊢ [𝐅 q]) (by simp) (by simp)
      exact .impL (A := 𝐆 (p ⇒ q)) (B := 𝐅 q) (by simp)
        (.ax (A := 𝐆 (p ⇒ q)) (by simp) (by simp))
        (.ax (A := 𝐅 q) (by simp) (by simp))
    · exact .impL (A := 𝐆 (p ⇒ q)) (B := 𝐅 q) (by simp)
        (.ax (A := 𝐆 (p ⇒ q)) (by simp) (by simp))
        (.ax (A := 𝐅 q) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ q))] ⊢ [(𝐆 (𝐅 (p)) ⇒ 𝐆 (𝐅 (q)))] :=
  Candidate.candidate p q

#print axioms verified
