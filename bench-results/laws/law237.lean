import LTL

open LTL

-- LTL law 237: ◇ q ⟹ ¬□ p ∨ p U q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐅 (q)] ⊢ [(∼(𝐆 (p)) ⋎ (p 𝐔 q))] := by
  have inner : [𝐆 p, (∼(𝐆 p)) ⋎ (p 𝐔 q)] ⊢ [p 𝐔 q] :=
    Derives.orL (A := ∼(𝐆 p)) (B := p 𝐔 q) (by simp)
      (Derives.negL (A := 𝐆 p) (by simp)
        (Derives.ax (A := 𝐆 p) (by simp) (by simp)))
      (Derives.ax (A := p 𝐔 q) (by simp) (by simp))
  have base : [q] ⊢ [(∼(𝐆 p)) ⋎ (p 𝐔 q)] :=
    Derives.orR (A := ∼(𝐆 p)) (B := p 𝐔 q) (by simp)
      (Derives.untilR (A := p) (B := q) (by simp)
        (Derives.ax (A := q) (by simp) (by simp))
        (Derives.ax (A := q) (by simp) (by simp)))
  have stepc : [𝐗 ((∼(𝐆 p)) ⋎ (p 𝐔 q))] ⊢ [(∼(𝐆 p)) ⋎ (p 𝐔 q)] :=
    Derives.orR (A := ∼(𝐆 p)) (B := p 𝐔 q) (by simp)
      (Derives.negR (A := 𝐆 p) (by simp)
        (Derives.alwaysL (A := p) (by simp)
          (Derives.untilR (A := p) (B := q) (by simp)
            (Derives.ax (A := p) (by simp) (by simp))
            (Derives.step (Γ' := [𝐆 p, (∼(𝐆 p)) ⋎ (p 𝐔 q)]) (B := p 𝐔 q)
              inner (by simp) (by simp)))))
  exact Derives.evL (A := q) ((∼(𝐆 p)) ⋎ (p 𝐔 q)) (by simp) base stepc
    (Derives.ax (A := (∼(𝐆 p)) ⋎ (p 𝐔 q)) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐅 (q)] ⊢ [(∼(𝐆 (p)) ⋎ (p 𝐔 q))] :=
  Candidate.candidate p q

#print axioms verified
