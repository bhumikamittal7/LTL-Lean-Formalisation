import LTL

open LTL

-- LTL law 19: (p ⇒ q) U r ⟹ (p U r) ⇒ (q U r)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q r : Formula AP) :
    [((p ⇒ q) 𝐔 r)] ⊢ [((p 𝐔 r) ⇒ (q 𝐔 r))] :=
  Derives.untilL (A := p ⇒ q) (B := r) ((p 𝐔 r) ⇒ (q 𝐔 r)) (by simp)
    (Derives.impR (A := p 𝐔 r) (B := q 𝐔 r) (by simp)
      (Derives.untilR (A := q) (B := r) (by simp)
        (Derives.ax (A := r) (by simp) (by simp))
        (Derives.ax (A := r) (by simp) (by simp))))
    (Derives.impR (A := p 𝐔 r) (B := q 𝐔 r) (by simp)
      (Derives.untilL (A := p) (B := r) (r ⋎ (p ⋏ 𝐗 (p 𝐔 r))) (by simp)
        (Derives.orR (A := r) (B := p ⋏ 𝐗 (p 𝐔 r)) (by simp)
          (Derives.ax (A := r) (by simp) (by simp)))
        (Derives.orR (A := r) (B := p ⋏ 𝐗 (p 𝐔 r)) (by simp)
          (Derives.andR (A := p) (B := 𝐗 (p 𝐔 r)) (by simp)
            (Derives.ax (A := p) (by simp) (by simp))
            (Derives.step (Γ' := [r ⋎ (p ⋏ 𝐗 (p 𝐔 r))]) (B := p 𝐔 r)
              (Derives.orL (A := r) (B := p ⋏ 𝐗 (p 𝐔 r)) (by simp)
                (Derives.untilR (A := p) (B := r) (by simp)
                  (Derives.ax (A := r) (by simp) (by simp))
                  (Derives.ax (A := r) (by simp) (by simp)))
                (Derives.andL (A := p) (B := 𝐗 (p 𝐔 r)) (by simp)
                  (Derives.untilR (A := p) (B := r) (by simp)
                    (Derives.ax (A := p) (by simp) (by simp))
                    (Derives.ax (A := 𝐗 (p 𝐔 r)) (by simp) (by simp)))))
              (by simp) (by simp))))
        (Derives.orL (A := r) (B := p ⋏ 𝐗 (p 𝐔 r)) (by simp)
          (Derives.untilR (A := q) (B := r) (by simp)
            (Derives.ax (A := r) (by simp) (by simp))
            (Derives.ax (A := r) (by simp) (by simp)))
          (Derives.andL (A := p) (B := 𝐗 (p 𝐔 r)) (by simp)
            (Derives.impL (A := p) (B := q) (by simp)
              (Derives.ax (A := p) (by simp) (by simp))
              (Derives.untilR (A := q) (B := r) (by simp)
                (Derives.ax (A := q) (by simp) (by simp))
                (Derives.step (Γ' := [p 𝐔 r, (p 𝐔 r) ⇒ (q 𝐔 r)]) (B := q 𝐔 r)
                  (Derives.impL (A := p 𝐔 r) (B := q 𝐔 r) (by simp)
                    (Derives.ax (A := p 𝐔 r) (by simp) (by simp))
                    (Derives.ax (A := q 𝐔 r) (by simp) (by simp)))
                  (by simp) (by simp))))))))
    (Derives.ax (A := (p 𝐔 r) ⇒ (q 𝐔 r)) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    [((p ⇒ q) 𝐔 r)] ⊢ [((p 𝐔 r) ⇒ (q 𝐔 r))] :=
  Candidate.candidate p q r

#print axioms verified
