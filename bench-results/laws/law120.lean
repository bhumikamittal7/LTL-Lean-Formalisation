import LTL

open LTL

-- LTL law 120: □ (p ⇒ q) ⟹ (□ p ⇒ □ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ q))] ⊢ [(𝐆 (p) ⇒ 𝐆 (q))] := by
  apply Derives.impR (A := 𝐆 p) (B := 𝐆 q) (by simp)
  apply Derives.alwaysR (A := q) (I := 𝐆 p ⋏ 𝐆 (p ⇒ q)) (by simp)
  · exact Derives.andR (A := 𝐆 p) (B := 𝐆 (p ⇒ q)) (by simp)
      (.ax (A := 𝐆 p) (by simp) (by simp))
      (.ax (A := 𝐆 (p ⇒ q)) (by simp) (by simp))
  · apply Derives.andL (A := 𝐆 p) (B := 𝐆 (p ⇒ q)) (by simp)
    apply Derives.alwaysL (A := p) (by simp)
    apply Derives.alwaysL (A := p ⇒ q) (by simp)
    exact Derives.step (Γ' := [𝐆 p, 𝐆 (p ⇒ q)]) (B := 𝐆 p ⋏ 𝐆 (p ⇒ q))
      (Derives.andR (A := 𝐆 p) (B := 𝐆 (p ⇒ q)) (by simp)
        (.ax (A := 𝐆 p) (by simp) (by simp))
        (.ax (A := 𝐆 (p ⇒ q)) (by simp) (by simp)))
      (by simp) (by simp)
  · apply Derives.andL (A := 𝐆 p) (B := 𝐆 (p ⇒ q)) (by simp)
    apply Derives.alwaysL (A := p) (by simp)
    apply Derives.alwaysL (A := p ⇒ q) (by simp)
    exact Derives.impL (A := p) (B := q) (by simp)
      (.ax (A := p) (by simp) (by simp))
      (.ax (A := q) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ q))] ⊢ [(𝐆 (p) ⇒ 𝐆 (q))] :=
  Candidate.candidate p q

#print axioms verified
