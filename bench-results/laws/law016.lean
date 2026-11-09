import LTL

open LTL

-- LTL law 16: (p U q) ∧ (¬q U r) ⟹ p U r
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem untilUnfold {AP : Type} (p q : Formula AP) :
    [p 𝐔 q] ⊢ [q, p ⋏ (𝐗 (p 𝐔 q))] := by
  refine Derives.untilL (A := p) (B := q) (I := q ⋎ (p ⋏ (𝐗 (p 𝐔 q)))) (by simp) ?_ ?_ ?_
  · exact Derives.orR (A := q) (B := p ⋏ (𝐗 (p 𝐔 q))) (by simp)
      (Derives.ax (A := q) (by simp) (by simp))
  · refine Derives.orR (A := q) (B := p ⋏ (𝐗 (p 𝐔 q))) (by simp) ?_
    refine Derives.andR (A := p) (B := 𝐗 (p 𝐔 q)) (by simp) ?_ ?_
    · exact Derives.ax (A := p) (by simp) (by simp)
    · refine Derives.step (Γ' := [q ⋎ (p ⋏ (𝐗 (p 𝐔 q)))]) (B := p 𝐔 q) ?_ (by simp) (by simp)
      refine Derives.orL (A := q) (B := p ⋏ (𝐗 (p 𝐔 q))) (by simp) ?_ ?_
      · refine Derives.untilR (A := p) (B := q) (by simp) ?_ ?_
        · exact Derives.ax (A := q) (by simp) (by simp)
        · exact Derives.ax (A := q) (by simp) (by simp)
      · refine Derives.andL (A := p) (B := 𝐗 (p 𝐔 q)) (by simp) ?_
        refine Derives.untilR (A := p) (B := q) (by simp) ?_ ?_
        · exact Derives.ax (A := p) (by simp) (by simp)
        · exact Derives.ax (A := 𝐗 (p 𝐔 q)) (by simp) (by simp)
  · refine Derives.orL (A := q) (B := p ⋏ (𝐗 (p 𝐔 q))) (by simp) ?_ ?_
    · exact Derives.ax (A := q) (by simp) (by simp)
    · exact Derives.ax (A := p ⋏ (𝐗 (p 𝐔 q))) (by simp) (by simp)

theorem candidate {AP : Type} (p q r : Formula AP) :
    [((p 𝐔 q) ⋏ (∼(q) 𝐔 r))] ⊢ [(p 𝐔 r)] := by
  refine Derives.andL (A := p 𝐔 q) (B := ∼(q) 𝐔 r) (by simp) ?_
  refine Derives.untilL (A := ∼(q)) (B := r) (I := (p 𝐔 q) ⇒ (p 𝐔 r)) (by simp) ?_ ?_ ?_
  · -- [r] ⊢ [I]
    refine Derives.impR (A := p 𝐔 q) (B := p 𝐔 r) (by simp) ?_
    refine Derives.untilR (A := p) (B := r) (by simp) ?_ ?_
    · exact Derives.ax (A := r) (by simp) (by simp)
    · exact Derives.ax (A := r) (by simp) (by simp)
  · -- [∼q, 𝐗 I] ⊢ [I]
    refine Derives.impR (A := p 𝐔 q) (B := p 𝐔 r) (by simp) ?_
    refine Derives.cut (p ⋏ (𝐗 (p 𝐔 q))) ?_ ?_
    · refine Derives.cut q ?_ ?_
      · exact Derives.wk (untilUnfold p q) (by simp) (by simp)
      · refine Derives.negL (A := q) (by simp) ?_
        exact Derives.ax (A := q) (by simp) (by simp)
    · refine Derives.andL (A := p) (B := 𝐗 (p 𝐔 q)) (by simp) ?_
      refine Derives.untilR (A := p) (B := r) (by simp) ?_ ?_
      · exact Derives.ax (A := p) (by simp) (by simp)
      · refine Derives.step (Γ' := [(p 𝐔 q) ⇒ (p 𝐔 r), p 𝐔 q]) (B := p 𝐔 r) ?_ (by simp) (by simp)
        refine Derives.impL (A := p 𝐔 q) (B := p 𝐔 r) (by simp) ?_ ?_
        · exact Derives.ax (A := p 𝐔 q) (by simp) (by simp)
        · exact Derives.ax (A := p 𝐔 r) (by simp) (by simp)
  · -- I :: Γ ⊢ [p 𝐔 r]
    refine Derives.impL (A := p 𝐔 q) (B := p 𝐔 r) (by simp) ?_ ?_
    · exact Derives.ax (A := p 𝐔 q) (by simp) (by simp)
    · exact Derives.ax (A := p 𝐔 r) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [((p 𝐔 q) ⋏ (∼(q) 𝐔 r))] ⊢ [(p 𝐔 r)] :=
  Candidate.candidate p q r

#print axioms verified
