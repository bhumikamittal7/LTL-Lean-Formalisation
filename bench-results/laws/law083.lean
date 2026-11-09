import LTL

open LTL

-- LTL law 83: □ p ∧ q U r ⟹ (p ∧ q) U (p ∧ r)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r : Formula AP) :
    [(𝐆 (p) ⋏ (q 𝐔 r))] ⊢ [((p ⋏ q) 𝐔 (p ⋏ r))] := by
  refine Derives.andL (A := 𝐆 p) (B := q 𝐔 r) (by simp) ?_
  refine Derives.untilL (A := q) (B := r) (I := (𝐆 p ⇒ ((p ⋏ q) 𝐔 (p ⋏ r)))) (by simp) ?_ ?_ ?_
  · refine Derives.impR (A := 𝐆 p) (B := (p ⋏ q) 𝐔 (p ⋏ r)) (by simp) ?_
    refine Derives.alwaysL (A := p) (by simp) ?_
    refine Derives.untilR (A := p ⋏ q) (B := p ⋏ r) (by simp) ?_ ?_
    · refine Derives.andR (A := p) (B := r) (by simp) ?_ ?_
      · exact .ax (A := p) (by simp) (by simp)
      · exact .ax (A := r) (by simp) (by simp)
    · refine Derives.andR (A := p) (B := r) (by simp) ?_ ?_
      · exact .ax (A := p) (by simp) (by simp)
      · exact .ax (A := r) (by simp) (by simp)
  · refine Derives.impR (A := 𝐆 p) (B := (p ⋏ q) 𝐔 (p ⋏ r)) (by simp) ?_
    refine Derives.alwaysL (A := p) (by simp) ?_
    refine Derives.untilR (A := p ⋏ q) (B := p ⋏ r) (by simp) ?_ ?_
    · refine Derives.andR (A := p) (B := q) (by simp) ?_ ?_
      · exact .ax (A := p) (by simp) (by simp)
      · exact .ax (A := q) (by simp) (by simp)
    · refine Derives.step (Γ' := [(𝐆 p ⇒ ((p ⋏ q) 𝐔 (p ⋏ r))), 𝐆 p])
        (B := (p ⋏ q) 𝐔 (p ⋏ r)) ?_ (by simp) (by simp)
      refine Derives.impL (A := 𝐆 p) (B := (p ⋏ q) 𝐔 (p ⋏ r)) (by simp) ?_ ?_
      · exact .ax (A := 𝐆 p) (by simp) (by simp)
      · exact .ax (A := (p ⋏ q) 𝐔 (p ⋏ r)) (by simp) (by simp)
  · refine Derives.impL (A := 𝐆 p) (B := (p ⋏ q) 𝐔 (p ⋏ r)) (by simp) ?_ ?_
    · exact .ax (A := 𝐆 p) (by simp) (by simp)
    · exact .ax (A := (p ⋏ q) 𝐔 (p ⋏ r)) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [(𝐆 (p) ⋏ (q 𝐔 r))] ⊢ [((p ⋏ q) 𝐔 (p ⋏ r))] :=
  Candidate.candidate p q r

#print axioms verified
