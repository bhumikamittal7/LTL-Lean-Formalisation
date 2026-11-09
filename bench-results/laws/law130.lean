import LTL

open LTL

-- LTL law 130: □ (p ⇒ ¬q ∧ ◯ p) ⟹ (p ⇒ ¬(r U q))
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r : Formula AP) :
    [𝐆 ((p ⇒ (∼(q) ⋏ 𝐗 (p))))] ⊢ [(p ⇒ ∼((r 𝐔 q)))] := by
  refine Derives.impR (A := p) (B := ∼((r 𝐔 q))) (by simp) ?_
  refine Derives.negR (A := (r 𝐔 q)) (by simp) ?_
  refine Derives.untilL (A := r) (B := q)
    (I := (𝐆 ((p ⇒ (∼(q) ⋏ 𝐗 (p))))) ⇒ ∼(p)) (by simp) ?_ ?_ ?_
  · -- base: [q] ⊢ [I]
    refine Derives.impR (A := 𝐆 ((p ⇒ (∼(q) ⋏ 𝐗 (p))))) (B := ∼(p)) (by simp) ?_
    refine Derives.negR (A := p) (by simp) ?_
    refine Derives.alwaysL (A := (p ⇒ (∼(q) ⋏ 𝐗 (p)))) (by simp) ?_
    refine Derives.impL (A := p) (B := (∼(q) ⋏ 𝐗 (p))) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · refine Derives.andL (A := ∼(q)) (B := 𝐗 (p)) (by simp) ?_
      refine Derives.negL (A := q) (by simp) ?_
      exact .ax (A := q) (by simp) (by simp)
  · -- step: [r, 𝐗 I] ⊢ [I]
    refine Derives.impR (A := 𝐆 ((p ⇒ (∼(q) ⋏ 𝐗 (p))))) (B := ∼(p)) (by simp) ?_
    refine Derives.negR (A := p) (by simp) ?_
    refine Derives.alwaysL (A := (p ⇒ (∼(q) ⋏ 𝐗 (p)))) (by simp) ?_
    refine Derives.impL (A := p) (B := (∼(q) ⋏ 𝐗 (p))) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · refine Derives.andL (A := ∼(q)) (B := 𝐗 (p)) (by simp) ?_
      refine Derives.next
        (Γ' := [(𝐆 ((p ⇒ (∼(q) ⋏ 𝐗 (p))))) ⇒ ∼(p), 𝐆 ((p ⇒ (∼(q) ⋏ 𝐗 (p)))), p])
        (Δ' := ([] : List (Formula AP))) ?_ (by simp) (by simp)
      refine Derives.impL (A := 𝐆 ((p ⇒ (∼(q) ⋏ 𝐗 (p))))) (B := ∼(p)) (by simp) ?_ ?_
      · exact .ax (A := 𝐆 ((p ⇒ (∼(q) ⋏ 𝐗 (p))))) (by simp) (by simp)
      · refine Derives.negL (A := p) (by simp) ?_
        exact .ax (A := p) (by simp) (by simp)
  · -- use: I :: Γ ⊢ Δ
    refine Derives.impL (A := 𝐆 ((p ⇒ (∼(q) ⋏ 𝐗 (p))))) (B := ∼(p)) (by simp) ?_ ?_
    · exact .ax (A := 𝐆 ((p ⇒ (∼(q) ⋏ 𝐗 (p))))) (by simp) (by simp)
    · refine Derives.negL (A := p) (by simp) ?_
      exact .ax (A := p) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [𝐆 ((p ⇒ (∼(q) ⋏ 𝐗 (p))))] ⊢ [(p ⇒ ∼((r 𝐔 q)))] :=
  Candidate.candidate p q r

#print axioms verified
