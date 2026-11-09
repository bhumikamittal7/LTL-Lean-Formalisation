import LTL

open LTL

-- LTL law 45: ◇ p ≈ p ∨ ◯ ◇ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem dir2_aux {AP : Type} (p : Formula AP) :
    [(p ⋎ 𝐗 (𝐅 (p)))] ⊢ [𝐅 (p)] :=
  Derives.evR (A := p) (by simp)
    (Derives.orL (A := p) (B := 𝐗 (𝐅 (p))) (by simp)
      (.ax (A := p) (by simp) (by simp))
      (.ax (A := 𝐗 (𝐅 (p))) (by simp) (by simp)))

theorem dir1_aux {AP : Type} (p : Formula AP) :
    [𝐅 (p)] ⊢ [(p ⋎ 𝐗 (𝐅 (p)))] :=
  Derives.evL (A := p) (p ⋎ 𝐗 (𝐅 (p))) (by simp)
    (Derives.orR (A := p) (B := 𝐗 (𝐅 (p))) (by simp)
      (.ax (A := p) (by simp) (by simp)))
    (Derives.orR (A := p) (B := 𝐗 (𝐅 (p))) (by simp)
      (Derives.step (Γ' := [(p ⋎ 𝐗 (𝐅 (p)))]) (dir2_aux p) (by simp) (by simp)))
    (.ax (A := (p ⋎ 𝐗 (𝐅 (p)))) (by simp) (by simp))

theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐅 (p)] ⊢ [(p ⋎ 𝐗 (𝐅 (p)))]) ∧ ([(p ⋎ 𝐗 (𝐅 (p)))] ⊢ [𝐅 (p)]) :=
  ⟨dir1_aux p, dir2_aux p⟩

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐅 (p)] ⊢ [(p ⋎ 𝐗 (𝐅 (p)))]) ∧ ([(p ⋎ 𝐗 (𝐅 (p)))] ⊢ [𝐅 (p)]) :=
  Candidate.candidate p

#print axioms verified
