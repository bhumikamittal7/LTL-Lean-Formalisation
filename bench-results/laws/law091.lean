import LTL

open LTL

-- LTL law 91: ◇ p ∨ ◇ ¬p ≈ ⊤
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p : Formula AP) :
    ([(𝐅 (p) ⋎ 𝐅 (∼(p)))] ⊢ [⊤ₗ]) ∧ ([⊤ₗ] ⊢ [(𝐅 (p) ⋎ 𝐅 (∼(p)))]) := by
  refine ⟨?_, ?_⟩
  · exact Derives.topR (by simp)
  · exact Derives.orR (A := 𝐅 (p)) (B := 𝐅 (∼(p))) (by simp)
      (Derives.evR (A := p) (by simp)
        (Derives.evR (A := ∼(p)) (by simp)
          (Derives.negR (A := p) (by simp)
            (Derives.ax (A := p) (by simp) (by simp)))))

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([(𝐅 (p) ⋎ 𝐅 (∼(p)))] ⊢ [⊤ₗ]) ∧ ([⊤ₗ] ⊢ [(𝐅 (p) ⋎ 𝐅 (∼(p)))]) :=
  Candidate.candidate p

#print axioms verified
