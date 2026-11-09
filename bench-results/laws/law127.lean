import LTL

open LTL

-- LTL law 127: □ ((p ⇒ r) ∧ (q ⇒ s)) ⟹ (p U q ⇒ r U s)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r s : Formula AP) :
    [𝐆 (((p ⇒ r) ⋏ (q ⇒ s)))] ⊢ [((p 𝐔 q) ⇒ (r 𝐔 s))] := by
  refine Derives.impR (A := p 𝐔 q) (B := r 𝐔 s) (by simp) ?_
  refine Derives.untilL (A := p) (B := q)
    ((𝐆 (((p ⇒ r) ⋏ (q ⇒ s)))) ⇒ (r 𝐔 s)) (by simp) ?_ ?_ ?_
  · -- [q] ⊢ [I]
    refine Derives.impR (A := 𝐆 (((p ⇒ r) ⋏ (q ⇒ s)))) (B := r 𝐔 s) (by simp) ?_
    refine Derives.alwaysL (A := ((p ⇒ r) ⋏ (q ⇒ s))) (by simp) ?_
    refine Derives.andL (A := (p ⇒ r)) (B := (q ⇒ s)) (by simp) ?_
    refine Derives.untilR (A := r) (B := s) (by simp) ?_ ?_
    · exact Derives.impL (A := q) (B := s) (by simp)
        (.ax (A := q) (by simp) (by simp)) (.ax (A := s) (by simp) (by simp))
    · exact Derives.impL (A := q) (B := s) (by simp)
        (.ax (A := q) (by simp) (by simp)) (.ax (A := s) (by simp) (by simp))
  · -- [p, X I] ⊢ [I]
    refine Derives.impR (A := 𝐆 (((p ⇒ r) ⋏ (q ⇒ s)))) (B := r 𝐔 s) (by simp) ?_
    refine Derives.alwaysL (A := ((p ⇒ r) ⋏ (q ⇒ s))) (by simp) ?_
    refine Derives.andL (A := (p ⇒ r)) (B := (q ⇒ s)) (by simp) ?_
    refine Derives.untilR (A := r) (B := s) (by simp) ?_ ?_
    · exact Derives.impL (A := p) (B := r) (by simp)
        (.ax (A := p) (by simp) (by simp)) (.ax (A := r) (by simp) (by simp))
    · refine Derives.step
        (Γ' := [𝐆 (((p ⇒ r) ⋏ (q ⇒ s))), ((𝐆 (((p ⇒ r) ⋏ (q ⇒ s)))) ⇒ (r 𝐔 s))])
        (B := r 𝐔 s) ?_ (by simp) (by simp)
      exact Derives.impL (A := 𝐆 (((p ⇒ r) ⋏ (q ⇒ s)))) (B := r 𝐔 s) (by simp)
        (.ax (A := 𝐆 (((p ⇒ r) ⋏ (q ⇒ s)))) (by simp) (by simp))
        (.ax (A := r 𝐔 s) (by simp) (by simp))
  · -- I :: Γ ⊢ Δ
    exact Derives.impL (A := 𝐆 (((p ⇒ r) ⋏ (q ⇒ s)))) (B := r 𝐔 s) (by simp)
      (.ax (A := 𝐆 (((p ⇒ r) ⋏ (q ⇒ s)))) (by simp) (by simp))
      (.ax (A := r 𝐔 s) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q r s : Formula AP) :
    [𝐆 (((p ⇒ r) ⋏ (q ⇒ s)))] ⊢ [((p 𝐔 q) ⇒ (r 𝐔 s))] :=
  Candidate.candidate p q r s

#print axioms verified
