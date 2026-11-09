import LTL

open LTL

-- LTL law 56: □ (p ⇒ ◯ (p ∨ q)) ⟹ p ⇒ □ p ∨ p U q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ 𝐗 ((p ⋎ q))))] ⊢ [(p ⇒ (𝐆 (p) ⋎ (p 𝐔 q)))] := by
  refine .impR (A := p) (B := (𝐆 p) ⋎ (p 𝐔 q)) (by simp) ?_
  refine .orR (A := 𝐆 p) (B := p 𝐔 q) (by simp) ?_
  refine .alwaysR (A := p)
    (I := p ⋏ ((𝐆 (p ⇒ 𝐗 (p ⋎ q))) ⋏ (∼(p 𝐔 q)))) (by simp) ?_ ?_ ?_
  · refine .andR (A := p) (B := (𝐆 (p ⇒ 𝐗 (p ⋎ q))) ⋏ (∼(p 𝐔 q))) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · refine .andR (A := 𝐆 (p ⇒ 𝐗 (p ⋎ q))) (B := ∼(p 𝐔 q)) (by simp) ?_ ?_
      · exact .ax (A := 𝐆 (p ⇒ 𝐗 (p ⋎ q))) (by simp) (by simp)
      · refine .negR (A := p 𝐔 q) (by simp) ?_
        exact .ax (A := p 𝐔 q) (by simp) (by simp)
  · refine .andL (A := p) (B := (𝐆 (p ⇒ 𝐗 (p ⋎ q))) ⋏ (∼(p 𝐔 q))) (by simp) ?_
    refine .andL (A := 𝐆 (p ⇒ 𝐗 (p ⋎ q))) (B := ∼(p 𝐔 q)) (by simp) ?_
    refine .alwaysL (A := p ⇒ 𝐗 (p ⋎ q)) (by simp) ?_
    refine .impL (A := p) (B := 𝐗 (p ⋎ q)) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · refine .negL (A := p 𝐔 q) (by simp) ?_
      refine .untilR (A := p) (B := q) (by simp) ?_ ?_
      · exact .ax (A := p) (by simp) (by simp)
      · refine .next (Γ' := [p ⋎ q, 𝐆 (p ⇒ 𝐗 (p ⋎ q))])
          (Δ' := [p 𝐔 q, p ⋏ ((𝐆 (p ⇒ 𝐗 (p ⋎ q))) ⋏ (∼(p 𝐔 q)))]) ?_ (by simp) (by simp)
        refine .orL (A := p) (B := q) (by simp) ?_ ?_
        · refine .andR (A := p) (B := (𝐆 (p ⇒ 𝐗 (p ⋎ q))) ⋏ (∼(p 𝐔 q))) (by simp) ?_ ?_
          · exact .ax (A := p) (by simp) (by simp)
          · refine .andR (A := 𝐆 (p ⇒ 𝐗 (p ⋎ q))) (B := ∼(p 𝐔 q)) (by simp) ?_ ?_
            · exact .ax (A := 𝐆 (p ⇒ 𝐗 (p ⋎ q))) (by simp) (by simp)
            · refine .negR (A := p 𝐔 q) (by simp) ?_
              exact .ax (A := p 𝐔 q) (by simp) (by simp)
        · refine .untilR (A := p) (B := q) (by simp) ?_ ?_
          · exact .ax (A := q) (by simp) (by simp)
          · exact .ax (A := q) (by simp) (by simp)
  · refine .andL (A := p) (B := (𝐆 (p ⇒ 𝐗 (p ⋎ q))) ⋏ (∼(p 𝐔 q))) (by simp) ?_
    exact .ax (A := p) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ 𝐗 ((p ⋎ q))))] ⊢ [(p ⇒ (𝐆 (p) ⋎ (p 𝐔 q)))] :=
  Candidate.candidate p q

#print axioms verified
