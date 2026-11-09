import LTL

open LTL

-- LTL law 55: □ (p ⇒ (◯ p ∧ q) ∨ r) ⟹ p ⇒ □ q ∨ q U r
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem cand_rebuild {AP : Type} (p q r : Formula AP) :
    [p, 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))] ⊢
      [(q 𝐔 r), (p ⋏ (∼(q 𝐔 r) ⋏ 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))))] :=
  .andR (A := p) (B := (∼(q 𝐔 r) ⋏ 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r))))) (by simp)
    (.ax (A := p) (by simp) (by simp))
    (.andR (A := ∼(q 𝐔 r)) (B := 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))) (by simp)
      (.negR (A := (q 𝐔 r)) (by simp) (.ax (A := (q 𝐔 r)) (by simp) (by simp)))
      (.ax (A := 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))) (by simp) (by simp)))

theorem cand_pres {AP : Type} (p q r : Formula AP) :
    [(p ⋏ (∼(q 𝐔 r) ⋏ 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))))] ⊢
      [𝐗 (p ⋏ (∼(q 𝐔 r) ⋏ 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))))] :=
  .andL (A := p) (B := (∼(q 𝐔 r) ⋏ 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r))))) (by simp)
  (.andL (A := ∼(q 𝐔 r)) (B := 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))) (by simp)
   (.alwaysL (A := (p ⇒ ((𝐗 (p) ⋏ q) ⋎ r))) (by simp)
    (.impL (A := p) (B := ((𝐗 (p) ⋏ q) ⋎ r)) (by simp)
      (.ax (A := p) (by simp) (by simp))
      (.orL (A := (𝐗 (p) ⋏ q)) (B := r) (by simp)
        (.andL (A := 𝐗 (p)) (B := q) (by simp)
          (.negL (A := (q 𝐔 r)) (by simp)
            (.untilR (A := q) (B := r) (by simp)
              (.ax (A := q) (by simp) (by simp))
              (.next (Γ' := [p, 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))])
                (Δ' := [(q 𝐔 r), (p ⋏ (∼(q 𝐔 r) ⋏ 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))))])
                (cand_rebuild p q r) (by simp) (by simp)))))
        (.negL (A := (q 𝐔 r)) (by simp)
          (.untilR (A := q) (B := r) (by simp)
            (.ax (A := r) (by simp) (by simp))
            (.ax (A := r) (by simp) (by simp))))))))

theorem cand_goal {AP : Type} (p q r : Formula AP) :
    [(p ⋏ (∼(q 𝐔 r) ⋏ 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))))] ⊢ [q] :=
  .andL (A := p) (B := (∼(q 𝐔 r) ⋏ 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r))))) (by simp)
  (.andL (A := ∼(q 𝐔 r)) (B := 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))) (by simp)
   (.alwaysL (A := (p ⇒ ((𝐗 (p) ⋏ q) ⋎ r))) (by simp)
    (.impL (A := p) (B := ((𝐗 (p) ⋏ q) ⋎ r)) (by simp)
      (.ax (A := p) (by simp) (by simp))
      (.orL (A := (𝐗 (p) ⋏ q)) (B := r) (by simp)
        (.andL (A := 𝐗 (p)) (B := q) (by simp)
          (.ax (A := q) (by simp) (by simp)))
        (.negL (A := (q 𝐔 r)) (by simp)
          (.untilR (A := q) (B := r) (by simp)
            (.ax (A := r) (by simp) (by simp))
            (.ax (A := r) (by simp) (by simp))))))))

theorem candidate {AP : Type} (p q r : Formula AP) :
    [𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))] ⊢ [(p ⇒ (𝐆 (q) ⋎ (q 𝐔 r)))] :=
  .impR (A := p) (B := (𝐆 (q) ⋎ (q 𝐔 r))) (by simp)
    (.orR (A := 𝐆 (q)) (B := (q 𝐔 r)) (by simp)
      (.alwaysR (A := q)
        (p ⋏ (∼(q 𝐔 r) ⋏ 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))))
        (by simp)
        (.andR (A := p) (B := (∼(q 𝐔 r) ⋏ 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r))))) (by simp)
          (.ax (A := p) (by simp) (by simp))
          (.andR (A := ∼(q 𝐔 r)) (B := 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))) (by simp)
            (.negR (A := (q 𝐔 r)) (by simp) (.ax (A := (q 𝐔 r)) (by simp) (by simp)))
            (.ax (A := 𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))) (by simp) (by simp))))
        (cand_pres p q r)
        (cand_goal p q r)))

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [𝐆 ((p ⇒ ((𝐗 (p) ⋏ q) ⋎ r)))] ⊢ [(p ⇒ (𝐆 (q) ⋎ (q 𝐔 r)))] :=
  Candidate.candidate p q r

#print axioms verified
