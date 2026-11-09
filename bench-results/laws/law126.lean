import LTL

open LTL

-- LTL law 126: □ ((p ⇒ q U r) ∧ (r ⇒ q U s)) ⟹ (p ⇒ q U s)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate_base {AP : Type} (p q r s : Formula AP) :
    [r] ⊢ [((𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s))))) ⇒ (q 𝐔 s))] :=
  .impR (A := 𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s))))) (B := q 𝐔 s) (by simp) <|
  .alwaysL (A := ((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s)))) (by simp) <|
  .andL (A := (p ⇒ (q 𝐔 r))) (B := (r ⇒ (q 𝐔 s))) (by simp) <|
  .impL (A := r) (B := q 𝐔 s) (by simp)
    (.ax (A := r) (by simp) (by simp))
    (.ax (A := q 𝐔 s) (by simp) (by simp))

theorem candidate_next {AP : Type} (p q r s : Formula AP) :
    [𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s)))),
     ((𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s))))) ⇒ (q 𝐔 s))] ⊢ [q 𝐔 s] :=
  .impL (A := 𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s))))) (B := q 𝐔 s) (by simp)
    (.ax (A := 𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s))))) (by simp) (by simp))
    (.ax (A := q 𝐔 s) (by simp) (by simp))

theorem candidate_step {AP : Type} (p q r s : Formula AP) :
    [q, 𝐗 ((𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s))))) ⇒ (q 𝐔 s))] ⊢
      [((𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s))))) ⇒ (q 𝐔 s))] :=
  .impR (A := 𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s))))) (B := q 𝐔 s) (by simp) <|
  .alwaysL (A := ((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s)))) (by simp) <|
  .untilR (A := q) (B := s) (by simp)
    (.ax (A := q) (by simp) (by simp))
    (Derives.step
      (Γ' := [𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s)))),
              ((𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s))))) ⇒ (q 𝐔 s))])
      (B := q 𝐔 s)
      (candidate_next p q r s) (by simp) (by simp))

theorem candidate {AP : Type} (p q r s : Formula AP) :
    [𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s))))] ⊢ [(p ⇒ (q 𝐔 s))] :=
  .impR (A := p) (B := q 𝐔 s) (by simp) <|
  .alwaysL (A := ((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s)))) (by simp) <|
  .andL (A := (p ⇒ (q 𝐔 r))) (B := (r ⇒ (q 𝐔 s))) (by simp) <|
  .impL (A := p) (B := q 𝐔 r) (by simp) (.ax (A := p) (by simp) (by simp)) <|
  .untilL (A := q) (B := r)
    (I := ((𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s))))) ⇒ (q 𝐔 s)))
    (by simp) (candidate_base p q r s) (candidate_step p q r s) <|
  .impL (A := 𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s))))) (B := q 𝐔 s) (by simp)
    (.ax (A := 𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s))))) (by simp) (by simp))
    (.ax (A := q 𝐔 s) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q r s : Formula AP) :
    [𝐆 (((p ⇒ (q 𝐔 r)) ⋏ (r ⇒ (q 𝐔 s))))] ⊢ [(p ⇒ (q 𝐔 s))] :=
  Candidate.candidate p q r s

#print axioms verified
