import LTL

open LTL

-- LTL law 168: ◇ □ p ∧ □ (□ p ⇒ ◇ q) ⟹ ◇ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [(𝐅 (𝐆 (p)) ⋏ 𝐆 ((𝐆 (p) ⇒ 𝐅 (q))))] ⊢ [𝐅 (q)] := by
  refine Derives.andL (A := 𝐅 (𝐆 p)) (B := 𝐆 (𝐆 p ⇒ 𝐅 q)) (by simp) ?_
  refine Derives.evL (A := 𝐆 p) (I := (𝐆 (𝐆 p ⇒ 𝐅 q) ⇒ 𝐅 q)) (by simp) ?_ ?_ ?_
  · refine Derives.impR (A := 𝐆 (𝐆 p ⇒ 𝐅 q)) (B := 𝐅 q) (by simp) ?_
    refine Derives.alwaysL (A := (𝐆 p ⇒ 𝐅 q)) (by simp) ?_
    refine Derives.impL (A := 𝐆 p) (B := 𝐅 q) (by simp) ?_ ?_
    · exact Derives.ax (A := 𝐆 p) (by simp) (by simp)
    · exact Derives.ax (A := 𝐅 q) (by simp) (by simp)
  · refine Derives.impR (A := 𝐆 (𝐆 p ⇒ 𝐅 q)) (B := 𝐅 q) (by simp) ?_
    refine Derives.alwaysL (A := (𝐆 p ⇒ 𝐅 q)) (by simp) ?_
    refine Derives.evR (A := q) (by simp) ?_
    refine Derives.step (Γ' := [(𝐆 (𝐆 p ⇒ 𝐅 q) ⇒ 𝐅 q), 𝐆 (𝐆 p ⇒ 𝐅 q)]) (B := 𝐅 q)
      ?_ (by simp) (by simp)
    refine Derives.impL (A := 𝐆 (𝐆 p ⇒ 𝐅 q)) (B := 𝐅 q) (by simp) ?_ ?_
    · exact Derives.ax (A := 𝐆 (𝐆 p ⇒ 𝐅 q)) (by simp) (by simp)
    · exact Derives.ax (A := 𝐅 q) (by simp) (by simp)
  · refine Derives.impL (A := 𝐆 (𝐆 p ⇒ 𝐅 q)) (B := 𝐅 q) (by simp) ?_ ?_
    · exact Derives.ax (A := 𝐆 (𝐆 p ⇒ 𝐅 q)) (by simp) (by simp)
    · exact Derives.ax (A := 𝐅 q) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [(𝐅 (𝐆 (p)) ⋏ 𝐆 ((𝐆 (p) ⇒ 𝐅 (q))))] ⊢ [𝐅 (q)] :=
  Candidate.candidate p q

#print axioms verified
