import LTL

open LTL

-- LTL law 104: ◇ (p ⇒ q) ≈ (□ p ⇒ ◇ q)
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem dir1_ev_imp {AP : Type} (p q : Formula AP) :
    [𝐅 ((p ⇒ q))] ⊢ [(𝐆 (p) ⇒ 𝐅 (q))] := by
  refine Derives.impR (A := 𝐆 p) (B := 𝐅 q) (by simp) ?_
  refine Derives.evL (A := p ⇒ q) (I := 𝐆 p ⇒ 𝐅 q) (by simp) ?_ ?_ ?_
  · refine Derives.impR (A := 𝐆 p) (B := 𝐅 q) (by simp) ?_
    refine Derives.alwaysL (A := p) (by simp) ?_
    refine Derives.impL (A := p) (B := q) (by simp) ?_ ?_
    · exact .ax (A := p) (by simp) (by simp)
    · refine Derives.evR (A := q) (by simp) ?_
      exact .ax (A := q) (by simp) (by simp)
  · refine Derives.impR (A := 𝐆 p) (B := 𝐅 q) (by simp) ?_
    refine Derives.alwaysL (A := p) (by simp) ?_
    refine Derives.evR (A := q) (by simp) ?_
    have h : [𝐆 p, 𝐆 p ⇒ 𝐅 q] ⊢ [𝐅 q] := by
      refine Derives.impL (A := 𝐆 p) (B := 𝐅 q) (by simp) ?_ ?_
      · exact .ax (A := 𝐆 p) (by simp) (by simp)
      · exact .ax (A := 𝐅 q) (by simp) (by simp)
    exact Derives.step h (by simp) (by simp)
  · exact .ax (A := 𝐆 p ⇒ 𝐅 q) (by simp) (by simp)

theorem dir2_ev_imp {AP : Type} (p q : Formula AP) :
    [(𝐆 (p) ⇒ 𝐅 (q))] ⊢ [𝐅 ((p ⇒ q))] := by
  refine Derives.impL (A := 𝐆 p) (B := 𝐅 q) (by simp) ?_ ?_
  · refine Derives.alwaysR (A := p) (I := ∼ (𝐅 (p ⇒ q))) (by simp) ?_ ?_ ?_
    · refine Derives.negR (A := 𝐅 (p ⇒ q)) (by simp) ?_
      exact .ax (A := 𝐅 (p ⇒ q)) (by simp) (by simp)
    · refine Derives.negL (A := 𝐅 (p ⇒ q)) (by simp) ?_
      refine Derives.evR (A := p ⇒ q) (by simp) ?_
      have h : ([] : List (Formula AP)) ⊢ [𝐅 (p ⇒ q), ∼ (𝐅 (p ⇒ q))] := by
        refine Derives.negR (A := 𝐅 (p ⇒ q)) (by simp) ?_
        exact .ax (A := 𝐅 (p ⇒ q)) (by simp) (by simp)
      exact Derives.next h (by simp) (by simp)
    · refine Derives.negL (A := 𝐅 (p ⇒ q)) (by simp) ?_
      refine Derives.evR (A := p ⇒ q) (by simp) ?_
      refine Derives.impR (A := p) (B := q) (by simp) ?_
      exact .ax (A := p) (by simp) (by simp)
  · refine Derives.evL (A := q) (I := 𝐅 (p ⇒ q)) (by simp) ?_ ?_ ?_
    · refine Derives.evR (A := p ⇒ q) (by simp) ?_
      refine Derives.impR (A := p) (B := q) (by simp) ?_
      exact .ax (A := q) (by simp) (by simp)
    · refine Derives.evR (A := p ⇒ q) (by simp) ?_
      exact .ax (A := 𝐗 (𝐅 (p ⇒ q))) (by simp) (by simp)
    · exact .ax (A := 𝐅 (p ⇒ q)) (by simp) (by simp)

theorem candidate {AP : Type} (p q : Formula AP) :
    ([𝐅 ((p ⇒ q))] ⊢ [(𝐆 (p) ⇒ 𝐅 (q))]) ∧ ([(𝐆 (p) ⇒ 𝐅 (q))] ⊢ [𝐅 ((p ⇒ q))]) :=
  ⟨dir1_ev_imp p q, dir2_ev_imp p q⟩

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([𝐅 ((p ⇒ q))] ⊢ [(𝐆 (p) ⇒ 𝐅 (q))]) ∧ ([(𝐆 (p) ⇒ 𝐅 (q))] ⊢ [𝐅 ((p ⇒ q))]) :=
  Candidate.candidate p q

#print axioms verified
