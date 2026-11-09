import LTL

open LTL

-- LTL law 121: □ ((p ⇒ q) ∧ (q ⇒ ◯ r) ∧ (r ⇒ s)) ⟹ (p ⇒ ◯ s)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r s : Formula AP) :
    [𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐗 (r)) ⋏ (r ⇒ s))))] ⊢ [(p ⇒ 𝐗 (s))] := by
  have h2 : [r, 𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐗 (r)) ⋏ (r ⇒ s))))] ⊢ [s] := by
    refine Derives.alwaysL (A := ((p ⇒ q) ⋏ ((q ⇒ 𝐗 (r)) ⋏ (r ⇒ s)))) (by simp) ?_
    refine Derives.andL (A := (p ⇒ q)) (B := ((q ⇒ 𝐗 (r)) ⋏ (r ⇒ s))) (by simp) ?_
    refine Derives.andL (A := (q ⇒ 𝐗 (r))) (B := (r ⇒ s)) (by simp) ?_
    refine Derives.impL (A := r) (B := s) (by simp) ?_ ?_
    · exact Derives.ax (A := r) (by simp) (by simp)
    · exact Derives.ax (A := s) (by simp) (by simp)
  refine Derives.impR (A := p) (B := 𝐗 (s)) (by simp) ?_
  refine Derives.alwaysL (A := ((p ⇒ q) ⋏ ((q ⇒ 𝐗 (r)) ⋏ (r ⇒ s)))) (by simp) ?_
  refine Derives.andL (A := (p ⇒ q)) (B := ((q ⇒ 𝐗 (r)) ⋏ (r ⇒ s))) (by simp) ?_
  refine Derives.andL (A := (q ⇒ 𝐗 (r))) (B := (r ⇒ s)) (by simp) ?_
  refine Derives.impL (A := p) (B := q) (by simp) ?_ ?_
  · exact Derives.ax (A := p) (by simp) (by simp)
  refine Derives.impL (A := q) (B := 𝐗 (r)) (by simp) ?_ ?_
  · exact Derives.ax (A := q) (by simp) (by simp)
  exact Derives.step (Γ' := [r, 𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐗 (r)) ⋏ (r ⇒ s))))]) h2
    (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q r s : Formula AP) :
    [𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐗 (r)) ⋏ (r ⇒ s))))] ⊢ [(p ⇒ 𝐗 (s))] :=
  Candidate.candidate p q r s

#print axioms verified
