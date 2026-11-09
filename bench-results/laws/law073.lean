import LTL

open LTL

-- LTL law 73: ◯ □ p ≈ □ ◯ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐗 (𝐆 (p))] ⊢ [𝐆 (𝐗 (p))]) ∧ ([𝐆 (𝐗 (p))] ⊢ [𝐗 (𝐆 (p))]) := by
  constructor
  · exact .alwaysR (A := 𝐗 p) (I := 𝐗 (𝐆 p)) (by simp)
      (.ax (A := 𝐗 (𝐆 p)) (by simp) (by simp))
      (.step (Γ' := [𝐆 p]) (B := 𝐗 (𝐆 p))
        (.alwaysL (A := p) (by simp) (.ax (A := 𝐗 (𝐆 p)) (by simp) (by simp)))
        (by simp) (by simp))
      (.step (Γ' := [𝐆 p]) (B := p)
        (.alwaysL (A := p) (by simp) (.ax (A := p) (by simp) (by simp)))
        (by simp) (by simp))
  · exact .alwaysL (A := 𝐗 p) (by simp)
      (.step (Γ' := [𝐆 (𝐗 p), p]) (B := 𝐆 p)
        (.alwaysR (A := p) (I := (p ⋏ (𝐆 (𝐗 p)))) (by simp)
          (.andR (A := p) (B := 𝐆 (𝐗 p)) (by simp)
            (.ax (A := p) (by simp) (by simp))
            (.ax (A := 𝐆 (𝐗 p)) (by simp) (by simp)))
          (.andL (A := p) (B := 𝐆 (𝐗 p)) (by simp)
            (.alwaysL (A := 𝐗 p) (by simp)
              (.step (Γ' := [p, 𝐆 (𝐗 p)]) (B := (p ⋏ (𝐆 (𝐗 p))))
                (.andR (A := p) (B := 𝐆 (𝐗 p)) (by simp)
                  (.ax (A := p) (by simp) (by simp))
                  (.ax (A := 𝐆 (𝐗 p)) (by simp) (by simp)))
                (by simp) (by simp))))
          (.andL (A := p) (B := 𝐆 (𝐗 p)) (by simp)
            (.ax (A := p) (by simp) (by simp))))
        (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐗 (𝐆 (p))] ⊢ [𝐆 (𝐗 (p))]) ∧ ([𝐆 (𝐗 (p))] ⊢ [𝐗 (𝐆 (p))]) :=
  Candidate.candidate p

#print axioms verified
