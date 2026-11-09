import LTL

open LTL

-- LTL law 86: □ (p ⇒ q) ⟹ (p U r ⇒ q U r)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r : Formula AP) :
    [𝐆 ((p ⇒ q))] ⊢ [((p 𝐔 r) ⇒ (q 𝐔 r))] := by
  refine Derives.impR (A := p 𝐔 r) (B := q 𝐔 r) (by simp) ?_
  refine Derives.untilL (A := p) (B := r) ((𝐆 (p ⇒ q)) ⇒ (q 𝐔 r)) (by simp) ?_ ?_ ?_
  · refine Derives.impR (A := 𝐆 (p ⇒ q)) (B := q 𝐔 r) (by simp) ?_
    refine Derives.untilR (A := q) (B := r) (by simp) ?_ ?_
    · exact .ax (A := r) (by simp) (by simp)
    · exact .ax (A := r) (by simp) (by simp)
  · refine Derives.impR (A := 𝐆 (p ⇒ q)) (B := q 𝐔 r) (by simp) ?_
    refine Derives.untilR (A := q) (B := r) (by simp) ?_ ?_
    · refine Derives.alwaysL (A := p ⇒ q) (by simp) ?_
      refine Derives.impL (A := p) (B := q) (by simp) ?_ ?_
      · exact .ax (A := p) (by simp) (by simp)
      · exact .ax (A := q) (by simp) (by simp)
    · refine Derives.alwaysL (A := p ⇒ q) (by simp) ?_
      refine Derives.step (Γ' := [𝐆 (p ⇒ q), (𝐆 (p ⇒ q)) ⇒ (q 𝐔 r)]) (B := q 𝐔 r) ?_ ?_ ?_
      · refine Derives.impL (A := 𝐆 (p ⇒ q)) (B := q 𝐔 r) (by simp) ?_ ?_
        · exact .ax (A := 𝐆 (p ⇒ q)) (by simp) (by simp)
        · exact .ax (A := q 𝐔 r) (by simp) (by simp)
      · simp
      · simp
  · refine Derives.impL (A := 𝐆 (p ⇒ q)) (B := q 𝐔 r) (by simp) ?_ ?_
    · exact .ax (A := 𝐆 (p ⇒ q)) (by simp) (by simp)
    · exact .ax (A := q 𝐔 r) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [𝐆 ((p ⇒ q))] ⊢ [((p 𝐔 r) ⇒ (q 𝐔 r))] :=
  Candidate.candidate p q r

#print axioms verified
