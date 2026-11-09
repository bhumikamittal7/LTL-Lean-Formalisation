import LTL

open LTL

-- LTL law 123: □ ((p ⇒ q) ∧ (q ⇒ □ r) ∧ (r ⇒ s)) ⟹ (p ⇒ □ s)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate_pres {AP : Type} (p q r s : Formula AP) :
    [𝐆 r ⋏ 𝐆 ((p ⇒ q) ⋏ ((q ⇒ 𝐆 r) ⋏ (r ⇒ s)))] ⊢
      [𝐗 (𝐆 r ⋏ 𝐆 ((p ⇒ q) ⋏ ((q ⇒ 𝐆 r) ⋏ (r ⇒ s))))] := by
  exact
    Derives.andL (A := 𝐆 r) (B := 𝐆 ((p ⇒ q) ⋏ ((q ⇒ 𝐆 r) ⋏ (r ⇒ s)))) (by simp) <|
    Derives.alwaysL (A := r) (by simp) <|
    Derives.alwaysL (A := (p ⇒ q) ⋏ ((q ⇒ 𝐆 r) ⋏ (r ⇒ s))) (by simp) <|
    Derives.step (Γ' := [𝐆 r, 𝐆 ((p ⇒ q) ⋏ ((q ⇒ 𝐆 r) ⋏ (r ⇒ s)))])
      (B := 𝐆 r ⋏ 𝐆 ((p ⇒ q) ⋏ ((q ⇒ 𝐆 r) ⋏ (r ⇒ s))))
      (Derives.andR (A := 𝐆 r) (B := 𝐆 ((p ⇒ q) ⋏ ((q ⇒ 𝐆 r) ⋏ (r ⇒ s)))) (by simp)
        (Derives.ax (A := 𝐆 r) (by simp) (by simp))
        (Derives.ax (A := 𝐆 ((p ⇒ q) ⋏ ((q ⇒ 𝐆 r) ⋏ (r ⇒ s)))) (by simp) (by simp)))
      (by simp) (by simp)

theorem candidate_goal {AP : Type} (p q r s : Formula AP) :
    [𝐆 r ⋏ 𝐆 ((p ⇒ q) ⋏ ((q ⇒ 𝐆 r) ⋏ (r ⇒ s)))] ⊢ [s] := by
  exact
    Derives.andL (A := 𝐆 r) (B := 𝐆 ((p ⇒ q) ⋏ ((q ⇒ 𝐆 r) ⋏ (r ⇒ s)))) (by simp) <|
    Derives.alwaysL (A := r) (by simp) <|
    Derives.alwaysL (A := (p ⇒ q) ⋏ ((q ⇒ 𝐆 r) ⋏ (r ⇒ s))) (by simp) <|
    Derives.andL (A := p ⇒ q) (B := (q ⇒ 𝐆 r) ⋏ (r ⇒ s)) (by simp) <|
    Derives.andL (A := q ⇒ 𝐆 r) (B := r ⇒ s) (by simp) <|
    Derives.impL (A := r) (B := s) (by simp)
      (Derives.ax (A := r) (by simp) (by simp))
      (Derives.ax (A := s) (by simp) (by simp))

theorem candidate {AP : Type} (p q r s : Formula AP) :
    [𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐆 (r)) ⋏ (r ⇒ s))))] ⊢ [(p ⇒ 𝐆 (s))] := by
  exact
    Derives.impR (A := p) (B := 𝐆 s) (by simp) <|
    Derives.alwaysL (A := (p ⇒ q) ⋏ ((q ⇒ 𝐆 r) ⋏ (r ⇒ s))) (by simp) <|
    Derives.andL (A := p ⇒ q) (B := (q ⇒ 𝐆 r) ⋏ (r ⇒ s)) (by simp) <|
    Derives.andL (A := q ⇒ 𝐆 r) (B := r ⇒ s) (by simp) <|
    Derives.impL (A := p) (B := q) (by simp) (Derives.ax (A := p) (by simp) (by simp)) <|
    Derives.impL (A := q) (B := 𝐆 r) (by simp) (Derives.ax (A := q) (by simp) (by simp)) <|
    Derives.alwaysR (A := s) (𝐆 r ⋏ 𝐆 ((p ⇒ q) ⋏ ((q ⇒ 𝐆 r) ⋏ (r ⇒ s)))) (by simp)
      (Derives.andR (A := 𝐆 r) (B := 𝐆 ((p ⇒ q) ⋏ ((q ⇒ 𝐆 r) ⋏ (r ⇒ s)))) (by simp)
        (Derives.ax (A := 𝐆 r) (by simp) (by simp))
        (Derives.ax (A := 𝐆 ((p ⇒ q) ⋏ ((q ⇒ 𝐆 r) ⋏ (r ⇒ s)))) (by simp) (by simp)))
      (candidate_pres p q r s)
      (candidate_goal p q r s)

end Candidate

theorem verified {AP : Type} (p q r s : Formula AP) :
    [𝐆 (((p ⇒ q) ⋏ ((q ⇒ 𝐆 (r)) ⋏ (r ⇒ s))))] ⊢ [(p ⇒ 𝐆 (s))] :=
  Candidate.candidate p q r s

#print axioms verified
