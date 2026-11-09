import LTL

open LTL

-- LTL law 102: □ (p ≡ q) ⟹ (◇ p ≡ ◇ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem aux_ev_mono {AP : Type} (p q E : Formula AP)
    (hE : [p, E] ⊢ [q]) :
    [𝐅 p, 𝐆 E] ⊢ [𝐅 q] := by
  refine Derives.evL (A := p) ((𝐆 E) ⇒ (𝐅 q)) (by simp) ?_ ?_ ?_
  · refine Derives.impR (A := 𝐆 E) (B := 𝐅 q) (by simp) ?_
    refine Derives.alwaysL (A := E) (by simp) ?_
    refine Derives.evR (A := q) (by simp) ?_
    exact Derives.wk hE (by simp) (by simp)
  · refine Derives.impR (A := 𝐆 E) (B := 𝐅 q) (by simp) ?_
    refine Derives.alwaysL (A := E) (by simp) ?_
    refine Derives.evR (A := q) (by simp) ?_
    refine Derives.step (Γ' := [((𝐆 E) ⇒ (𝐅 q)), 𝐆 E]) (B := 𝐅 q) ?_ (by simp) (by simp)
    exact Derives.impL (A := 𝐆 E) (B := 𝐅 q) (by simp)
      (Derives.ax (A := 𝐆 E) (by simp) (by simp))
      (Derives.ax (A := 𝐅 q) (by simp) (by simp))
  · exact Derives.impL (A := 𝐆 E) (B := 𝐅 q) (by simp)
      (Derives.ax (A := 𝐆 E) (by simp) (by simp))
      (Derives.ax (A := 𝐅 q) (by simp) (by simp))

theorem candidate {AP : Type} (p q : Formula AP) :
    [𝐆 (((p ⇒ q) ⋏ (q ⇒ p)))] ⊢ [((𝐅 (p) ⇒ 𝐅 (q)) ⋏ (𝐅 (q) ⇒ 𝐅 (p)))] := by
  have hE1 : [p, ((p ⇒ q) ⋏ (q ⇒ p))] ⊢ [q] := by
    refine Derives.andL (A := (p ⇒ q)) (B := (q ⇒ p)) (by simp) ?_
    exact Derives.impL (A := p) (B := q) (by simp)
      (Derives.ax (A := p) (by simp) (by simp))
      (Derives.ax (A := q) (by simp) (by simp))
  have hE2 : [q, ((p ⇒ q) ⋏ (q ⇒ p))] ⊢ [p] := by
    refine Derives.andL (A := (p ⇒ q)) (B := (q ⇒ p)) (by simp) ?_
    exact Derives.impL (A := q) (B := p) (by simp)
      (Derives.ax (A := q) (by simp) (by simp))
      (Derives.ax (A := p) (by simp) (by simp))
  refine Derives.andR (A := (𝐅 p ⇒ 𝐅 q)) (B := (𝐅 q ⇒ 𝐅 p)) (by simp) ?_ ?_
  · refine Derives.impR (A := 𝐅 p) (B := 𝐅 q) (by simp) ?_
    exact Derives.wk (aux_ev_mono p q _ hE1) (by simp) (by simp)
  · refine Derives.impR (A := 𝐅 q) (B := 𝐅 p) (by simp) ?_
    exact Derives.wk (aux_ev_mono q p _ hE2) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    [𝐆 (((p ⇒ q) ⋏ (q ⇒ p)))] ⊢ [((𝐅 (p) ⇒ 𝐅 (q)) ⋏ (𝐅 (q) ⇒ 𝐅 (p)))] :=
  Candidate.candidate p q

#print axioms verified
