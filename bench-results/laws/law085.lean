import LTL

open LTL

-- LTL law 85: □ (p ⇒ q) ⟹ (r U p ⇒ r U q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r : Formula AP) :
    [𝐆 ((p ⇒ q))] ⊢ [((r 𝐔 p) ⇒ (r 𝐔 q))] := by
  refine Derives.impR (A := (r 𝐔 p)) (B := (r 𝐔 q)) (by simp) ?_
  refine Derives.untilL (A := r) (B := p) ((𝐆 (p ⇒ q)) ⇒ (r 𝐔 q)) (by simp) ?_ ?_ ?_
  · -- [p] ⊢ [I]
    refine Derives.impR (A := (𝐆 (p ⇒ q))) (B := (r 𝐔 q)) (by simp) ?_
    refine Derives.alwaysL (A := (p ⇒ q)) (by simp) ?_
    refine Derives.impL (A := p) (B := q) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · refine Derives.untilR (A := r) (B := q) (by simp) ?_ ?_
      · exact .ax (A := q) (by simp) (by simp)
      · exact .ax (A := q) (by simp) (by simp)
  · -- [r, X I] ⊢ [I]
    refine Derives.impR (A := (𝐆 (p ⇒ q))) (B := (r 𝐔 q)) (by simp) ?_
    refine Derives.alwaysL (A := (p ⇒ q)) (by simp) ?_
    refine Derives.untilR (A := r) (B := q) (by simp) ?_ ?_
    · exact .ax (A := r) (by simp) (by simp)
    · refine Derives.step (Γ' := [((𝐆 (p ⇒ q)) ⇒ (r 𝐔 q)), (𝐆 (p ⇒ q))])
        (B := (r 𝐔 q)) ?_ (by simp) (by simp)
      refine Derives.impL (A := (𝐆 (p ⇒ q))) (B := (r 𝐔 q)) (by simp) ?_ ?_
      · exact .ax (A := (𝐆 (p ⇒ q))) (by simp) (by simp)
      · exact .ax (A := (r 𝐔 q)) (by simp) (by simp)
  · -- I :: Γ ⊢ Δ
    refine Derives.impL (A := (𝐆 (p ⇒ q))) (B := (r 𝐔 q)) (by simp) ?_ ?_
    · exact .ax (A := (𝐆 (p ⇒ q))) (by simp) (by simp)
    · exact .ax (A := (r 𝐔 q)) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [𝐆 ((p ⇒ q))] ⊢ [((r 𝐔 p) ⇒ (r 𝐔 q))] :=
  Candidate.candidate p q r

#print axioms verified
