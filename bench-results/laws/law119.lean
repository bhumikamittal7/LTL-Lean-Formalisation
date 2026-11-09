import LTL

open LTL

-- LTL law 119: □ (p ⇒ q) ⟹ (◇ p ⇒ ◇ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ q))] ⊢ [(𝐅 (p) ⇒ 𝐅 (q))] := by
  refine Derives.impR (A := 𝐅 p) (B := 𝐅 q) (by simp) ?_
  refine Derives.evL (A := p) (𝐆 (p ⇒ q) ⇒ 𝐅 q) (by simp) ?_ ?_ ?_
  · refine Derives.impR (A := 𝐆 (p ⇒ q)) (B := 𝐅 q) (by simp) ?_
    refine Derives.alwaysL (A := p ⇒ q) (by simp) ?_
    refine Derives.impL (A := p) (B := q) (by simp) ?_ ?_
    · exact Derives.ax (A := p) (by simp) (by simp)
    · refine Derives.evR (A := q) (by simp) ?_
      exact Derives.ax (A := q) (by simp) (by simp)
  · refine Derives.impR (A := 𝐆 (p ⇒ q)) (B := 𝐅 q) (by simp) ?_
    refine Derives.alwaysL (A := p ⇒ q) (by simp) ?_
    refine Derives.evR (A := q) (by simp) ?_
    refine Derives.step (Γ' := [𝐆 (p ⇒ q), 𝐆 (p ⇒ q) ⇒ 𝐅 q]) (B := 𝐅 q) ?_ (by simp) (by simp)
    refine Derives.impL (A := 𝐆 (p ⇒ q)) (B := 𝐅 q) (by simp) ?_ ?_
    · exact Derives.ax (A := 𝐆 (p ⇒ q)) (by simp) (by simp)
    · exact Derives.ax (A := 𝐅 q) (by simp) (by simp)
  · refine Derives.impL (A := 𝐆 (p ⇒ q)) (B := 𝐅 q) (by simp) ?_ ?_
    · exact Derives.ax (A := 𝐆 (p ⇒ q)) (by simp) (by simp)
    · exact Derives.ax (A := 𝐅 q) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ q))] ⊢ [(𝐅 (p) ⇒ 𝐅 (q))] :=
  Candidate.candidate p q

#print axioms verified
