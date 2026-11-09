import LTL

open LTL

-- LTL law 103: □ (p ≡ q) ⟹ (□ p ≡ □ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem gHelp {AP : Type} (p q E : Formula AP) (h : [p, E] ⊢ [q]) :
    [𝐆 (E), 𝐆 (p)] ⊢ [𝐆 (q)] := by
  refine Derives.alwaysR (A := q) (I := (𝐆 (p)) ⋏ (𝐆 (E))) (by simp) ?_ ?_ ?_
  · exact Derives.andR (A := 𝐆 (p)) (B := 𝐆 (E)) (by simp)
      (Derives.ax (A := 𝐆 (p)) (by simp) (by simp))
      (Derives.ax (A := 𝐆 (E)) (by simp) (by simp))
  · exact Derives.andL (A := 𝐆 (p)) (B := 𝐆 (E)) (by simp)
      (Derives.alwaysL (A := p) (by simp)
        (Derives.alwaysL (A := E) (by simp)
          (Derives.step (Γ' := [𝐆 (p), 𝐆 (E)]) (B := (𝐆 (p)) ⋏ (𝐆 (E)))
            (Derives.andR (A := 𝐆 (p)) (B := 𝐆 (E)) (by simp)
              (Derives.ax (A := 𝐆 (p)) (by simp) (by simp))
              (Derives.ax (A := 𝐆 (E)) (by simp) (by simp)))
            (by simp) (by simp))))
  · exact Derives.andL (A := 𝐆 (p)) (B := 𝐆 (E)) (by simp)
      (Derives.alwaysL (A := p) (by simp)
        (Derives.alwaysL (A := E) (by simp)
          (Derives.wk h (by simp) (by simp))))

theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (((p ⇒ q) ⋏ (q ⇒ p)))] ⊢ [((𝐆 (p) ⇒ 𝐆 (q)) ⋏ (𝐆 (q) ⇒ 𝐆 (p)))] := by
  have hpq : [p, ((p ⇒ q) ⋏ (q ⇒ p))] ⊢ [q] :=
    Derives.andL (A := p ⇒ q) (B := q ⇒ p) (by simp)
      (Derives.impL (A := p) (B := q) (by simp)
        (Derives.ax (A := p) (by simp) (by simp))
        (Derives.ax (A := q) (by simp) (by simp)))
  have hqp : [q, ((p ⇒ q) ⋏ (q ⇒ p))] ⊢ [p] :=
    Derives.andL (A := p ⇒ q) (B := q ⇒ p) (by simp)
      (Derives.impL (A := q) (B := p) (by simp)
        (Derives.ax (A := q) (by simp) (by simp))
        (Derives.ax (A := p) (by simp) (by simp)))
  refine Derives.andR (A := 𝐆 (p) ⇒ 𝐆 (q)) (B := 𝐆 (q) ⇒ 𝐆 (p)) (by simp) ?_ ?_
  · exact Derives.impR (A := 𝐆 (p)) (B := 𝐆 (q)) (by simp)
      (Derives.wk (gHelp p q _ hpq) (by simp) (by simp))
  · exact Derives.impR (A := 𝐆 (q)) (B := 𝐆 (p)) (by simp)
      (Derives.wk (gHelp q p _ hqp) (by simp) (by simp))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (((p ⇒ q) ⋏ (q ⇒ p)))] ⊢ [((𝐆 (p) ⇒ 𝐆 (q)) ⋏ (𝐆 (q) ⇒ 𝐆 (p)))] :=
  Candidate.candidate p q

#print axioms verified
