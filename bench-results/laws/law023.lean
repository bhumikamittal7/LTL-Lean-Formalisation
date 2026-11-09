import LTL

open LTL

-- LTL law 23: (p U q) ∨ (p U ¬q) ≈ ⊤
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    ([((p 𝐔 q) ⋎ (p 𝐔 ∼(q)))] ⊢ [⊤ₗ]) ∧ ([⊤ₗ] ⊢ [((p 𝐔 q) ⋎ (p 𝐔 ∼(q)))]) := by
  refine ⟨Derives.topR (by simp), ?_⟩
  have h : ∀ Δ : List (Formula AP), (p 𝐔 ∼(q)) ∈ Δ → q ∈ Δ →
      ([(⊤ₗ : Formula AP)] ⊢ Δ) := by
    intro Δ h1 h2
    refine Derives.untilR (A := p) (B := ∼(q)) h1 ?_ ?_
    · exact Derives.negR (A := q) (by simp)
        (Derives.ax (A := q) (by simp) (by simp [h2]))
    · exact Derives.negR (A := q) (by simp)
        (Derives.ax (A := q) (by simp) (by simp [h2]))
  refine Derives.orR (A := p 𝐔 q) (B := p 𝐔 ∼(q)) (by simp) ?_
  refine Derives.untilR (A := p) (B := q) (by simp) ?_ ?_
  · exact h _ (by simp) (by simp)
  · exact h _ (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([((p 𝐔 q) ⋎ (p 𝐔 ∼(q)))] ⊢ [⊤ₗ]) ∧ ([⊤ₗ] ⊢ [((p 𝐔 q) ⋎ (p 𝐔 ∼(q)))]) :=
  Candidate.candidate p q

#print axioms verified
