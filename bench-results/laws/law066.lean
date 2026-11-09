import LTL

open LTL

-- LTL law 66: □ p ≈ p ∧ ◯ □ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem helper_always_unfold {AP : Type} (p : Formula AP) :
    [𝐆 (p)] ⊢ [(p ⋏ 𝐗 (𝐆 (p)))] :=
  .alwaysL (A := p) (by simp)
    (.andR (A := p) (B := 𝐗 (𝐆 p)) (by simp)
      (.ax (A := p) (by simp) (by simp))
      (.ax (A := 𝐗 (𝐆 p)) (by simp) (by simp)))

theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐆 (p)] ⊢ [(p ⋏ 𝐗 (𝐆 (p)))]) ∧ ([(p ⋏ 𝐗 (𝐆 (p)))] ⊢ [𝐆 (p)]) :=
  ⟨helper_always_unfold p,
   .alwaysR (A := p) (p ⋏ 𝐗 (𝐆 p)) (by simp)
     (.ax (A := p ⋏ 𝐗 (𝐆 p)) (by simp) (by simp))
     (.andL (A := p) (B := 𝐗 (𝐆 p)) (by simp)
       (Derives.step (Γ' := [𝐆 p]) (helper_always_unfold p) (by simp) (by simp)))
     (.andL (A := p) (B := 𝐗 (𝐆 p)) (by simp)
       (.ax (A := p) (by simp) (by simp)))⟩

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐆 (p)] ⊢ [(p ⋏ 𝐗 (𝐆 (p)))]) ∧ ([(p ⋏ 𝐗 (𝐆 (p)))] ⊢ [𝐆 (p)]) :=
  Candidate.candidate p

#print axioms verified
