import LTL

open LTL

-- LTL law 101: □ (p ≡ q) ⟹ (◯ p ≡ ◯ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem helper1 {AP : Type} (p q : Formula AP) :
    [𝐆 (((p ⇒ q) ⋏ (q ⇒ p))), p] ⊢ [q] :=
  .alwaysL (A := ((p ⇒ q) ⋏ (q ⇒ p))) (by simp)
    (.andL (A := (p ⇒ q)) (B := (q ⇒ p)) (by simp)
      (.impL (A := p) (B := q) (by simp)
        (.ax (A := p) (by simp) (by simp))
        (.ax (A := q) (by simp) (by simp))))

theorem helper2 {AP : Type} (p q : Formula AP) :
    [𝐆 (((p ⇒ q) ⋏ (q ⇒ p))), q] ⊢ [p] :=
  .alwaysL (A := ((p ⇒ q) ⋏ (q ⇒ p))) (by simp)
    (.andL (A := (p ⇒ q)) (B := (q ⇒ p)) (by simp)
      (.impL (A := q) (B := p) (by simp)
        (.ax (A := q) (by simp) (by simp))
        (.ax (A := p) (by simp) (by simp))))

theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (((p ⇒ q) ⋏ (q ⇒ p)))] ⊢ [((𝐗 (p) ⇒ 𝐗 (q)) ⋏ (𝐗 (q) ⇒ 𝐗 (p)))] :=
  .alwaysL (A := ((p ⇒ q) ⋏ (q ⇒ p))) (by simp)
    (.andR (A := (𝐗 (p) ⇒ 𝐗 (q))) (B := (𝐗 (q) ⇒ 𝐗 (p))) (by simp)
      (.impR (A := 𝐗 (p)) (B := 𝐗 (q)) (by simp)
        (Derives.step (Γ' := [𝐆 (((p ⇒ q) ⋏ (q ⇒ p))), p]) (B := q)
          (helper1 p q) (by simp) (by simp)))
      (.impR (A := 𝐗 (q)) (B := 𝐗 (p)) (by simp)
        (Derives.step (Γ' := [𝐆 (((p ⇒ q) ⋏ (q ⇒ p))), q]) (B := p)
          (helper2 p q) (by simp) (by simp))))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (((p ⇒ q) ⋏ (q ⇒ p)))] ⊢ [((𝐗 (p) ⇒ 𝐗 (q)) ⋏ (𝐗 (q) ⇒ 𝐗 (p)))] :=
  Candidate.candidate p q

#print axioms verified
