import LTL

open LTL

-- LTL law 37: (p U q) U q ≈ p U q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem until_dir1 {AP : Type} (p q : Formula AP) :
    [((p 𝐔 q) 𝐔 q)] ⊢ [(p 𝐔 q)] :=
  Derives.untilL (A := p 𝐔 q) (B := q) (I := p 𝐔 q) (by simp)
    (Derives.untilR (A := p) (B := q) (by simp)
      (Derives.ax (A := q) (by simp) (by simp))
      (Derives.ax (A := q) (by simp) (by simp)))
    (Derives.ax (A := p 𝐔 q) (by simp) (by simp))
    (Derives.ax (A := p 𝐔 q) (by simp) (by simp))

theorem until_dir2_step {AP : Type} (p q : Formula AP) :
    [p, 𝐗 ((p 𝐔 q) 𝐔 q)] ⊢ [((p 𝐔 q) 𝐔 q)] :=
  Derives.untilR (A := p 𝐔 q) (B := q) (by simp)
    (Derives.untilR (A := p) (B := q) (by simp)
      (Derives.ax (A := p) (by simp) (by simp))
      (Derives.step (Γ' := [((p 𝐔 q) 𝐔 q)]) (B := p 𝐔 q) (until_dir1 p q)
        (by simp) (by simp)))
    (Derives.ax (A := 𝐗 ((p 𝐔 q) 𝐔 q)) (by simp) (by simp))

theorem until_dir2 {AP : Type} (p q : Formula AP) :
    [(p 𝐔 q)] ⊢ [((p 𝐔 q) 𝐔 q)] :=
  Derives.untilL (A := p) (B := q) (I := (p 𝐔 q) 𝐔 q) (by simp)
    (Derives.untilR (A := p 𝐔 q) (B := q) (by simp)
      (Derives.ax (A := q) (by simp) (by simp))
      (Derives.ax (A := q) (by simp) (by simp)))
    (until_dir2_step p q)
    (Derives.ax (A := (p 𝐔 q) 𝐔 q) (by simp) (by simp))

theorem candidate {AP : Type} (p q : Formula AP) :
    ([((p 𝐔 q) 𝐔 q)] ⊢ [(p 𝐔 q)]) ∧ ([(p 𝐔 q)] ⊢ [((p 𝐔 q) 𝐔 q)]) :=
  ⟨until_dir1 p q, until_dir2 p q⟩

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([((p 𝐔 q) 𝐔 q)] ⊢ [(p 𝐔 q)]) ∧ ([(p 𝐔 q)] ⊢ [((p 𝐔 q) 𝐔 q)]) :=
  Candidate.candidate p q

#print axioms verified
