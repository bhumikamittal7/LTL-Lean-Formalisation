import LTL

open LTL

-- LTL law 75: p ∧ ◇ ¬p ⟹ ◇ (p ∧ ¬◯ p)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    [(p ⋏ 𝐅 (∼(p)))] ⊢ [𝐅 ((p ⋏ ∼(𝐗 (p))))] := by
  refine .andL (A := p) (B := 𝐅 (∼(p))) (by simp) ?_
  refine .evL (A := ∼(p)) (I := (p ⇒ 𝐅 ((p ⋏ ∼(𝐗 (p)))))) (by simp) ?_ ?_ ?_
  · -- [∼p] ⊢ [I]
    refine .impR (A := p) (B := 𝐅 ((p ⋏ ∼(𝐗 (p))))) (by simp) ?_
    refine .negL (A := p) (by simp) ?_
    exact .ax (A := p) (by simp) (by simp)
  · -- [𝐗 I] ⊢ [I]
    refine .impR (A := p) (B := 𝐅 ((p ⋏ ∼(𝐗 (p))))) (by simp) ?_
    refine .evR (A := (p ⋏ ∼(𝐗 (p)))) (by simp) ?_
    refine .andR (A := p) (B := ∼(𝐗 (p))) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · refine .negR (A := 𝐗 (p)) (by simp) ?_
      refine .next
        (show [p, (p ⇒ 𝐅 ((p ⋏ ∼(𝐗 (p)))))] ⊢ [𝐅 ((p ⋏ ∼(𝐗 (p))))] from
          .impL (A := p) (B := 𝐅 ((p ⋏ ∼(𝐗 (p))))) (by simp)
            (.ax (A := p) (by simp) (by simp))
            (.ax (A := 𝐅 ((p ⋏ ∼(𝐗 (p))))) (by simp) (by simp)))
        (by simp) (by simp)
  · -- I :: Γ ⊢ Δ
    refine .impL (A := p) (B := 𝐅 ((p ⋏ ∼(𝐗 (p))))) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · exact .ax (A := 𝐅 ((p ⋏ ∼(𝐗 (p))))) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    [(p ⋏ 𝐅 (∼(p)))] ⊢ [𝐅 ((p ⋏ ∼(𝐗 (p))))] :=
  Candidate.candidate p

#print axioms verified
