import LTL

open LTL

-- LTL law 128: □ (p ∨ ◯ q ⇒ q) ⟹ (◇ p ⇒ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (((p ⋎ 𝐗 (q)) ⇒ q))] ⊢ [(𝐅 (p) ⇒ q)] := by
  refine Derives.impR (A := 𝐅 p) (B := q) (by simp) ?_
  refine Derives.evL (A := p) ((𝐆 ((p ⋎ 𝐗 q) ⇒ q)) ⇒ q) (by simp) ?_ ?_ ?_
  · refine Derives.impR (A := 𝐆 ((p ⋎ 𝐗 q) ⇒ q)) (B := q) (by simp) ?_
    refine Derives.alwaysL (A := (p ⋎ 𝐗 q) ⇒ q) (by simp) ?_
    refine Derives.impL (A := p ⋎ 𝐗 q) (B := q) (by simp) ?_ ?_
    · refine Derives.orR (A := p) (B := 𝐗 q) (by simp) ?_
      exact Derives.ax (A := p) (by simp) (by simp)
    · exact Derives.ax (A := q) (by simp) (by simp)
  · refine Derives.impR (A := 𝐆 ((p ⋎ 𝐗 q) ⇒ q)) (B := q) (by simp) ?_
    refine Derives.alwaysL (A := (p ⋎ 𝐗 q) ⇒ q) (by simp) ?_
    refine Derives.impL (A := p ⋎ 𝐗 q) (B := q) (by simp) ?_ ?_
    · refine Derives.orR (A := p) (B := 𝐗 q) (by simp) ?_
      refine Derives.step (Γ' := [(𝐆 ((p ⋎ 𝐗 q) ⇒ q)) ⇒ q, 𝐆 ((p ⋎ 𝐗 q) ⇒ q)])
        (B := q) ?_ (by simp) (by simp)
      refine Derives.impL (A := 𝐆 ((p ⋎ 𝐗 q) ⇒ q)) (B := q) (by simp) ?_ ?_
      · exact Derives.ax (A := 𝐆 ((p ⋎ 𝐗 q) ⇒ q)) (by simp) (by simp)
      · exact Derives.ax (A := q) (by simp) (by simp)
    · exact Derives.ax (A := q) (by simp) (by simp)
  · refine Derives.impL (A := 𝐆 ((p ⋎ 𝐗 q) ⇒ q)) (B := q) (by simp) ?_ ?_
    · exact Derives.ax (A := 𝐆 ((p ⋎ 𝐗 q) ⇒ q)) (by simp) (by simp)
    · exact Derives.ax (A := q) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (((p ⋎ 𝐗 (q)) ⇒ q))] ⊢ [(𝐅 (p) ⇒ q)] :=
  Candidate.candidate p q

#print axioms verified
