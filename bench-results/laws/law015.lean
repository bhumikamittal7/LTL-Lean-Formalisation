import LTL

open LTL

-- LTL law 15: (p ∧ q) U r ≈ (p U r) ∧ (q U r)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem untilLeftAnd1 {AP : Type} (p q r : Formula AP) :
    [((p ⋏ q) 𝐔 r)] ⊢ [(p 𝐔 r)] :=
  .untilL (A := p ⋏ q) (B := r) (I := p 𝐔 r) (by simp)
    (.untilR (A := p) (B := r) (by simp)
      (.ax (A := r) (by simp) (by simp))
      (.ax (A := r) (by simp) (by simp)))
    (.untilR (A := p) (B := r) (by simp)
      (.andL (A := p) (B := q) (by simp) (.ax (A := p) (by simp) (by simp)))
      (.ax (A := 𝐗 (p 𝐔 r)) (by simp) (by simp)))
    (.ax (A := p 𝐔 r) (by simp) (by simp))

theorem untilLeftAnd2 {AP : Type} (p q r : Formula AP) :
    [((p ⋏ q) 𝐔 r)] ⊢ [(q 𝐔 r)] :=
  .untilL (A := p ⋏ q) (B := r) (I := q 𝐔 r) (by simp)
    (.untilR (A := q) (B := r) (by simp)
      (.ax (A := r) (by simp) (by simp))
      (.ax (A := r) (by simp) (by simp)))
    (.untilR (A := q) (B := r) (by simp)
      (.andL (A := p) (B := q) (by simp) (.ax (A := q) (by simp) (by simp)))
      (.ax (A := 𝐗 (q 𝐔 r)) (by simp) (by simp)))
    (.ax (A := q 𝐔 r) (by simp) (by simp))

theorem jUnfold {AP : Type} (q r : Formula AP) :
    [(r ⋎ (q ⋏ 𝐗 (q 𝐔 r)))] ⊢ [(q 𝐔 r)] :=
  Derives.orL (A := r) (B := q ⋏ 𝐗 (q 𝐔 r)) (by simp)
    (.untilR (A := q) (B := r) (by simp)
      (.ax (A := r) (by simp) (by simp))
      (.ax (A := r) (by simp) (by simp)))
    (.andL (A := q) (B := 𝐗 (q 𝐔 r)) (by simp)
      (.untilR (A := q) (B := r) (by simp)
        (.ax (A := q) (by simp) (by simp))
        (.ax (A := 𝐗 (q 𝐔 r)) (by simp) (by simp))))

theorem jBase {AP : Type} (q r : Formula AP) :
    [r] ⊢ [(r ⋎ (q ⋏ 𝐗 (q 𝐔 r)))] :=
  Derives.orR (A := r) (B := q ⋏ 𝐗 (q 𝐔 r)) (by simp)
    (.ax (A := r) (by simp) (by simp))

theorem jStep {AP : Type} (q r : Formula AP) :
    [q, 𝐗 (r ⋎ (q ⋏ 𝐗 (q 𝐔 r)))] ⊢ [(r ⋎ (q ⋏ 𝐗 (q 𝐔 r)))] :=
  Derives.orR (A := r) (B := q ⋏ 𝐗 (q 𝐔 r)) (by simp)
    (.andR (A := q) (B := 𝐗 (q 𝐔 r)) (by simp)
      (.ax (A := q) (by simp) (by simp))
      (Derives.step (Γ' := [(r ⋎ (q ⋏ 𝐗 (q 𝐔 r)))]) (B := q 𝐔 r)
        (jUnfold q r) (by simp) (by simp)))

theorem impLemma {AP : Type} (p q r : Formula AP) :
    [((q 𝐔 r) ⇒ ((p ⋏ q) 𝐔 r)), (q 𝐔 r)] ⊢ [((p ⋏ q) 𝐔 r)] :=
  .impL (A := q 𝐔 r) (B := (p ⋏ q) 𝐔 r) (by simp)
    (.ax (A := q 𝐔 r) (by simp) (by simp))
    (.ax (A := (p ⋏ q) 𝐔 r) (by simp) (by simp))

theorem iBase {AP : Type} (p q r : Formula AP) :
    [r] ⊢ [((q 𝐔 r) ⇒ ((p ⋏ q) 𝐔 r))] :=
  .impR (A := q 𝐔 r) (B := (p ⋏ q) 𝐔 r) (by simp)
    (.untilR (A := p ⋏ q) (B := r) (by simp)
      (.ax (A := r) (by simp) (by simp))
      (.ax (A := r) (by simp) (by simp)))

theorem iStep {AP : Type} (p q r : Formula AP) :
    [p, 𝐗 ((q 𝐔 r) ⇒ ((p ⋏ q) 𝐔 r))] ⊢ [((q 𝐔 r) ⇒ ((p ⋏ q) 𝐔 r))] :=
  .impR (A := q 𝐔 r) (B := (p ⋏ q) 𝐔 r) (by simp)
    (.untilL (A := q) (B := r) (I := r ⋎ (q ⋏ 𝐗 (q 𝐔 r))) (by simp)
      (jBase q r) (jStep q r)
      (Derives.orL (A := r) (B := q ⋏ 𝐗 (q 𝐔 r)) (by simp)
        (.untilR (A := p ⋏ q) (B := r) (by simp)
          (.ax (A := r) (by simp) (by simp))
          (.ax (A := r) (by simp) (by simp)))
        (.andL (A := q) (B := 𝐗 (q 𝐔 r)) (by simp)
          (.untilR (A := p ⋏ q) (B := r) (by simp)
            (.andR (A := p) (B := q) (by simp)
              (.ax (A := p) (by simp) (by simp))
              (.ax (A := q) (by simp) (by simp)))
            (Derives.step (Γ' := [((q 𝐔 r) ⇒ ((p ⋏ q) 𝐔 r)), (q 𝐔 r)])
              (B := (p ⋏ q) 𝐔 r) (impLemma p q r) (by simp) (by simp))))))

theorem candidate {AP : Type} (p q r : Formula AP) :
    ([((p ⋏ q) 𝐔 r)] ⊢ [((p 𝐔 r) ⋏ (q 𝐔 r))]) ∧ ([((p 𝐔 r) ⋏ (q 𝐔 r))] ⊢ [((p ⋏ q) 𝐔 r)]) := by
  refine ⟨?_, ?_⟩
  · exact .andR (A := p 𝐔 r) (B := q 𝐔 r) (by simp)
      (Derives.wk (untilLeftAnd1 p q r) (by simp) (by simp))
      (Derives.wk (untilLeftAnd2 p q r) (by simp) (by simp))
  · exact .andL (A := p 𝐔 r) (B := q 𝐔 r) (by simp)
      (.untilL (A := p) (B := r) (I := (q 𝐔 r) ⇒ ((p ⋏ q) 𝐔 r)) (by simp)
        (iBase p q r) (iStep p q r)
        (.impL (A := q 𝐔 r) (B := (p ⋏ q) 𝐔 r) (by simp)
          (.ax (A := q 𝐔 r) (by simp) (by simp))
          (.ax (A := (p ⋏ q) 𝐔 r) (by simp) (by simp))))

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    ([((p ⋏ q) 𝐔 r)] ⊢ [((p 𝐔 r) ⋏ (q 𝐔 r))]) ∧ ([((p 𝐔 r) ⋏ (q 𝐔 r))] ⊢ [((p ⋏ q) 𝐔 r)]) :=
  Candidate.candidate p q r

#print axioms verified
