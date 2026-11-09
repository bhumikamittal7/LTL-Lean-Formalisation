import LTL

open LTL

-- LTL law 12: p U (q ∨ r) ≈ (p U q) ∨ (p U r)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate_dir1 {AP : Type} (p q r : Formula AP) :
    [(p 𝐔 (q ⋎ r))] ⊢ [((p 𝐔 q) ⋎ (p 𝐔 r))] :=
  Derives.untilL (A := p) (B := (q ⋎ r)) (I := ((p 𝐔 q) ⋎ (p 𝐔 r))) (by simp)
    (Derives.orR (A := (p 𝐔 q)) (B := (p 𝐔 r)) (by simp)
      (Derives.orL (A := q) (B := r) (by simp)
        (Derives.untilR (A := p) (B := q) (by simp)
          (Derives.ax (A := q) (by simp) (by simp))
          (Derives.ax (A := q) (by simp) (by simp)))
        (Derives.untilR (A := p) (B := r) (by simp)
          (Derives.ax (A := r) (by simp) (by simp))
          (Derives.ax (A := r) (by simp) (by simp)))))
    (Derives.orR (A := (p 𝐔 q)) (B := (p 𝐔 r)) (by simp)
      (Derives.untilR (A := p) (B := q) (by simp)
        (Derives.ax (A := p) (by simp) (by simp))
        (Derives.untilR (A := p) (B := r) (by simp)
          (Derives.ax (A := p) (by simp) (by simp))
          (Derives.next (Γ' := [((p 𝐔 q) ⋎ (p 𝐔 r))]) (Δ' := [(p 𝐔 q), (p 𝐔 r)])
            (Derives.orL (A := (p 𝐔 q)) (B := (p 𝐔 r)) (by simp)
              (Derives.ax (A := (p 𝐔 q)) (by simp) (by simp))
              (Derives.ax (A := (p 𝐔 r)) (by simp) (by simp)))
            (by simp) (by simp)))))
    (Derives.ax (A := ((p 𝐔 q) ⋎ (p 𝐔 r))) (by simp) (by simp))

theorem candidate_dir2 {AP : Type} (p q r : Formula AP) :
    [((p 𝐔 q) ⋎ (p 𝐔 r))] ⊢ [(p 𝐔 (q ⋎ r))] :=
  Derives.orL (A := (p 𝐔 q)) (B := (p 𝐔 r)) (by simp)
    (Derives.untilL (A := p) (B := q) (I := (p 𝐔 (q ⋎ r))) (by simp)
      (Derives.untilR (A := p) (B := (q ⋎ r)) (by simp)
        (Derives.orR (A := q) (B := r) (by simp)
          (Derives.ax (A := q) (by simp) (by simp)))
        (Derives.orR (A := q) (B := r) (by simp)
          (Derives.ax (A := q) (by simp) (by simp))))
      (Derives.untilR (A := p) (B := (q ⋎ r)) (by simp)
        (Derives.ax (A := p) (by simp) (by simp))
        (Derives.ax (A := (𝐗 (p 𝐔 (q ⋎ r)))) (by simp) (by simp)))
      (Derives.ax (A := (p 𝐔 (q ⋎ r))) (by simp) (by simp)))
    (Derives.untilL (A := p) (B := r) (I := (p 𝐔 (q ⋎ r))) (by simp)
      (Derives.untilR (A := p) (B := (q ⋎ r)) (by simp)
        (Derives.orR (A := q) (B := r) (by simp)
          (Derives.ax (A := r) (by simp) (by simp)))
        (Derives.orR (A := q) (B := r) (by simp)
          (Derives.ax (A := r) (by simp) (by simp))))
      (Derives.untilR (A := p) (B := (q ⋎ r)) (by simp)
        (Derives.ax (A := p) (by simp) (by simp))
        (Derives.ax (A := (𝐗 (p 𝐔 (q ⋎ r)))) (by simp) (by simp)))
      (Derives.ax (A := (p 𝐔 (q ⋎ r))) (by simp) (by simp)))

theorem candidate {AP : Type} (p q r : Formula AP) :
    ([(p 𝐔 (q ⋎ r))] ⊢ [((p 𝐔 q) ⋎ (p 𝐔 r))]) ∧ ([((p 𝐔 q) ⋎ (p 𝐔 r))] ⊢ [(p 𝐔 (q ⋎ r))]) :=
  ⟨candidate_dir1 p q r, candidate_dir2 p q r⟩

end Candidate

theorem verified {AP : Type} (p q r : Formula AP) :
    ([(p 𝐔 (q ⋎ r))] ⊢ [((p 𝐔 q) ⋎ (p 𝐔 r))]) ∧ ([((p 𝐔 q) ⋎ (p 𝐔 r))] ⊢ [(p 𝐔 (q ⋎ r))]) :=
  Candidate.candidate p q r

#print axioms verified
