import LTL

open LTL

-- LTL law 144: (p ∧ q) U r ⟹ p U (q U r)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r : Formula AP) :
    [((p ⋏ q) 𝐔 r)] ⊢ [(p 𝐔 (q 𝐔 r))] :=
  .untilL (A := p ⋏ q) (B := r) (q 𝐔 r) (by simp)
    (.untilR (A := q) (B := r) (by simp)
      (.ax (A := r) (by simp) (by simp))
      (.ax (A := r) (by simp) (by simp)))
    (.andL (A := p) (B := q) (by simp)
      (.untilR (A := q) (B := r) (by simp)
        (.ax (A := q) (by simp) (by simp))
        (.ax (A := 𝐗 (q 𝐔 r)) (by simp) (by simp))))
    (.untilR (A := p) (B := q 𝐔 r) (by simp)
      (.ax (A := q 𝐔 r) (by simp) (by simp))
      (.ax (A := q 𝐔 r) (by simp) (by simp)))

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [((p ⋏ q) 𝐔 r)] ⊢ [(p 𝐔 (q 𝐔 r))] :=
  Candidate.candidate p q r

#print axioms verified
