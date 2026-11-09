import LTL

open LTL

-- LTL law 124: □ ((p ⇒ ◇ q) ∧ (q ⇒ ◇ r)) ⟹ (p ⇒ ◇ r)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r : Formula AP) :
    [𝐆 (((p ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐅 (r))))] ⊢ [(p ⇒ 𝐅 (r))] := by
  refine Derives.impR (A := p) (B := 𝐅 r) (by simp) ?_
  refine Derives.alwaysL (A := (p ⇒ 𝐅 q) ⋏ (q ⇒ 𝐅 r)) (by simp) ?_
  refine Derives.andL (A := p ⇒ 𝐅 q) (B := q ⇒ 𝐅 r) (by simp) ?_
  refine Derives.impL (A := p) (B := 𝐅 q) (by simp) ?_ ?_
  · exact .ax (A := p) (by simp) (by simp)
  refine Derives.evL (A := q)
    (I := 𝐆 ((p ⇒ 𝐅 q) ⋏ (q ⇒ 𝐅 r)) ⇒ 𝐅 r) (by simp) ?_ ?_ ?_
  · refine Derives.impR (A := 𝐆 ((p ⇒ 𝐅 q) ⋏ (q ⇒ 𝐅 r))) (B := 𝐅 r) (by simp) ?_
    refine Derives.alwaysL (A := (p ⇒ 𝐅 q) ⋏ (q ⇒ 𝐅 r)) (by simp) ?_
    refine Derives.andL (A := p ⇒ 𝐅 q) (B := q ⇒ 𝐅 r) (by simp) ?_
    refine Derives.impL (A := q) (B := 𝐅 r) (by simp) ?_ ?_
    · exact .ax (A := q) (by simp) (by simp)
    · exact .ax (A := 𝐅 r) (by simp) (by simp)
  · refine Derives.impR (A := 𝐆 ((p ⇒ 𝐅 q) ⋏ (q ⇒ 𝐅 r))) (B := 𝐅 r) (by simp) ?_
    refine Derives.evR (A := r) (by simp) ?_
    refine Derives.alwaysL (A := (p ⇒ 𝐅 q) ⋏ (q ⇒ 𝐅 r)) (by simp) ?_
    refine Derives.step
      (Γ' := [𝐆 ((p ⇒ 𝐅 q) ⋏ (q ⇒ 𝐅 r)), 𝐆 ((p ⇒ 𝐅 q) ⋏ (q ⇒ 𝐅 r)) ⇒ 𝐅 r])
      (B := 𝐅 r) ?_ (by simp) (by simp)
    refine Derives.impL (A := 𝐆 ((p ⇒ 𝐅 q) ⋏ (q ⇒ 𝐅 r))) (B := 𝐅 r) (by simp) ?_ ?_
    · exact .ax (A := 𝐆 ((p ⇒ 𝐅 q) ⋏ (q ⇒ 𝐅 r))) (by simp) (by simp)
    · exact .ax (A := 𝐅 r) (by simp) (by simp)
  · refine Derives.impL (A := 𝐆 ((p ⇒ 𝐅 q) ⋏ (q ⇒ 𝐅 r))) (B := 𝐅 r) (by simp) ?_ ?_
    · exact .ax (A := 𝐆 ((p ⇒ 𝐅 q) ⋏ (q ⇒ 𝐅 r))) (by simp) (by simp)
    · exact .ax (A := 𝐅 r) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [𝐆 (((p ⇒ 𝐅 (q)) ⋏ (q ⇒ 𝐅 (r))))] ⊢ [(p ⇒ 𝐅 (r))] :=
  Candidate.candidate p q r

#print axioms verified
