import LTL

open LTL

-- LTL law 158: □ (p ⇒ q) ⟹ (◇ □ p ⇒ ◇ □ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem gg_lemma {AP : Type} (p q : Formula AP) :
    [𝐆 p, 𝐆 (p ⇒ q)] ⊢ [𝐆 q] :=
  Derives.alwaysR (A := q) ((𝐆 p) ⋏ (𝐆 (p ⇒ q))) (by simp)
    (Derives.andR (A := 𝐆 p) (B := 𝐆 (p ⇒ q)) (by simp)
      (Derives.ax (A := 𝐆 p) (by simp) (by simp))
      (Derives.ax (A := 𝐆 (p ⇒ q)) (by simp) (by simp)))
    (Derives.andL (A := 𝐆 p) (B := 𝐆 (p ⇒ q)) (by simp)
      (Derives.alwaysL (A := p) (by simp)
        (Derives.alwaysL (A := (p ⇒ q)) (by simp)
          (Derives.step (Γ' := [𝐆 p, 𝐆 (p ⇒ q)]) (B := (𝐆 p) ⋏ (𝐆 (p ⇒ q)))
            (Derives.andR (A := 𝐆 p) (B := 𝐆 (p ⇒ q)) (by simp)
              (Derives.ax (A := 𝐆 p) (by simp) (by simp))
              (Derives.ax (A := 𝐆 (p ⇒ q)) (by simp) (by simp)))
            (by simp) (by simp)))))
    (Derives.andL (A := 𝐆 p) (B := 𝐆 (p ⇒ q)) (by simp)
      (Derives.alwaysL (A := p) (by simp)
        (Derives.alwaysL (A := (p ⇒ q)) (by simp)
          (Derives.impL (A := p) (B := q) (by simp)
            (Derives.ax (A := p) (by simp) (by simp))
            (Derives.ax (A := q) (by simp) (by simp))))))

theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ q))] ⊢ [(𝐅 (𝐆 (p)) ⇒ 𝐅 (𝐆 (q)))] :=
  Derives.impR (A := 𝐅 (𝐆 p)) (B := 𝐅 (𝐆 q)) (by simp)
    (Derives.evL (A := 𝐆 p) ((𝐆 (p ⇒ q)) ⇒ (𝐅 (𝐆 q))) (by simp)
      (Derives.impR (A := 𝐆 (p ⇒ q)) (B := 𝐅 (𝐆 q)) (by simp)
        (Derives.evR (A := 𝐆 q) (by simp)
          (Derives.wk (gg_lemma p q) (by simp) (by simp))))
      (Derives.impR (A := 𝐆 (p ⇒ q)) (B := 𝐅 (𝐆 q)) (by simp)
        (Derives.evR (A := 𝐆 q) (by simp)
          (Derives.alwaysL (A := (p ⇒ q)) (by simp)
            (Derives.step (Γ' := [(𝐆 (p ⇒ q)) ⇒ (𝐅 (𝐆 q)), 𝐆 (p ⇒ q)]) (B := 𝐅 (𝐆 q))
              (Derives.impL (A := 𝐆 (p ⇒ q)) (B := 𝐅 (𝐆 q)) (by simp)
                (Derives.ax (A := 𝐆 (p ⇒ q)) (by simp) (by simp))
                (Derives.ax (A := 𝐅 (𝐆 q)) (by simp) (by simp)))
              (by simp) (by simp)))))
      (Derives.impL (A := 𝐆 (p ⇒ q)) (B := 𝐅 (𝐆 q)) (by simp)
        (Derives.ax (A := 𝐆 (p ⇒ q)) (by simp) (by simp))
        (Derives.ax (A := 𝐅 (𝐆 q)) (by simp) (by simp))))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 ((p ⇒ q))] ⊢ [(𝐅 (𝐆 (p)) ⇒ 𝐅 (𝐆 (q)))] :=
  Candidate.candidate p q

#print axioms verified
