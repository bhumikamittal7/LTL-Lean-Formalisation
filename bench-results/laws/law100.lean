import LTL

open LTL

-- LTL law 100: □ p ∨ □ q ⟹ □ (p ∨ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [(𝐆 (p) ⋎ 𝐆 (q))] ⊢ [𝐆 ((p ⋎ q))] :=
  Derives.orL (A := 𝐆 p) (B := 𝐆 q) (by simp)
    (Derives.alwaysR (A := p ⋎ q) (𝐆 p) (by simp)
      (.ax (A := 𝐆 p) (by simp) (by simp))
      (.alwaysL (A := p) (by simp) (.ax (A := 𝐗 (𝐆 p)) (by simp) (by simp)))
      (.alwaysL (A := p) (by simp)
        (Derives.orR (A := p) (B := q) (by simp) (.ax (A := p) (by simp) (by simp)))))
    (Derives.alwaysR (A := p ⋎ q) (𝐆 q) (by simp)
      (.ax (A := 𝐆 q) (by simp) (by simp))
      (.alwaysL (A := q) (by simp) (.ax (A := 𝐗 (𝐆 q)) (by simp) (by simp)))
      (.alwaysL (A := q) (by simp)
        (Derives.orR (A := p) (B := q) (by simp) (.ax (A := q) (by simp) (by simp)))))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [(𝐆 (p) ⋎ 𝐆 (q))] ⊢ [𝐆 ((p ⋎ q))] :=
  Candidate.candidate p q

#print axioms verified
