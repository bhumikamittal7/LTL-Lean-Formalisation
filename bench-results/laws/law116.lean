import LTL

open LTL

-- LTL law 116: □ p ⟹ (◇ q ⇒ ◇ (p ≡ q))
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐅 (q) ⇒ 𝐅 (((p ⇒ q) ⋏ (q ⇒ p))))] := by
  apply Derives.impR (A := 𝐅 q) (B := 𝐅 ((p ⇒ q) ⋏ (q ⇒ p))) (by simp)
  apply Derives.evL (A := q) (I := (𝐆 p ⇒ 𝐅 ((p ⇒ q) ⋏ (q ⇒ p)))) (by simp)
  · apply Derives.impR (A := 𝐆 p) (B := 𝐅 ((p ⇒ q) ⋏ (q ⇒ p))) (by simp)
    apply Derives.alwaysL (A := p) (by simp)
    apply Derives.evR (A := (p ⇒ q) ⋏ (q ⇒ p)) (by simp)
    apply Derives.andR (A := p ⇒ q) (B := q ⇒ p) (by simp)
    · apply Derives.impR (A := p) (B := q) (by simp)
      exact .ax (A := q) (by simp) (by simp)
    · apply Derives.impR (A := q) (B := p) (by simp)
      exact .ax (A := p) (by simp) (by simp)
  · apply Derives.impR (A := 𝐆 p) (B := 𝐅 ((p ⇒ q) ⋏ (q ⇒ p))) (by simp)
    apply Derives.alwaysL (A := p) (by simp)
    apply Derives.evR (A := (p ⇒ q) ⋏ (q ⇒ p)) (by simp)
    apply Derives.next (Γ' := [𝐆 p ⇒ 𝐅 ((p ⇒ q) ⋏ (q ⇒ p)), 𝐆 p])
      (Δ' := [𝐅 ((p ⇒ q) ⋏ (q ⇒ p))])
    · apply Derives.impL (A := 𝐆 p) (B := 𝐅 ((p ⇒ q) ⋏ (q ⇒ p))) (by simp)
      · exact .ax (A := 𝐆 p) (by simp) (by simp)
      · exact .ax (A := 𝐅 ((p ⇒ q) ⋏ (q ⇒ p))) (by simp) (by simp)
    · intro A hA
      simp at hA
      rcases hA with rfl | rfl <;> simp
    · intro A hA
      simp at hA
      subst hA
      simp
  · apply Derives.impL (A := 𝐆 p) (B := 𝐅 ((p ⇒ q) ⋏ (q ⇒ p))) (by simp)
    · exact .ax (A := 𝐆 p) (by simp) (by simp)
    · exact .ax (A := 𝐅 ((p ⇒ q) ⋏ (q ⇒ p))) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (p)] ⊢ [(𝐅 (q) ⇒ 𝐅 (((p ⇒ q) ⋏ (q ⇒ p))))] :=
  Candidate.candidate p q

#print axioms verified
