import LTL

open LTL

-- LTL law 1: ◯ ¬p ≈ ¬◯ p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([𝐗 (∼(p))] ⊢ [∼(𝐗 (p))]) ∧ ([∼(𝐗 (p))] ⊢ [𝐗 (∼(p))]) := by
  refine ⟨?_, ?_⟩
  · have h : ([∼(p), p] : List (Formula AP)) ⊢ ([] : List (Formula AP)) :=
      Derives.negL (A := p) (by simp) (Derives.ax (A := p) (by simp) (by simp))
    exact Derives.negR (A := 𝐗 (p)) (by simp) (Derives.next h (by simp) (by simp))
  · have h : ([] : List (Formula AP)) ⊢ ([p, ∼(p)] : List (Formula AP)) :=
      Derives.negR (A := p) (by simp) (Derives.ax (A := p) (by simp) (by simp))
    exact Derives.negL (A := 𝐗 (p)) (by simp) (Derives.next h (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([𝐗 (∼(p))] ⊢ [∼(𝐗 (p))]) ∧ ([∼(𝐗 (p))] ⊢ [𝐗 (∼(p))]) :=
  Candidate.candidate p

#print axioms verified
