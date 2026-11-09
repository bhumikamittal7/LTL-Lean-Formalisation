import LTL

open LTL

-- LTL law 163: ◇ □ (p ⇒ □ q) ≈ ◇ □ ¬p ∨ ◇ □ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem d1_core {AP : Type} (p q : Formula AP) :
    [𝐆 (p ⇒ 𝐆 q)] ⊢ [𝐅 (𝐆 (∼p)) ⋎ 𝐅 (𝐆 q)] := by
  refine Derives.orR (A := 𝐅 (𝐆 (∼p))) (B := 𝐅 (𝐆 q)) (by simp) ?_
  refine Derives.cut (A := 𝐅 p) ?_ ?_
  · refine Derives.evR (A := 𝐆 (∼p)) (by simp) ?_
    refine Derives.alwaysR (A := ∼p) (I := ∼(𝐅 p)) (by simp) ?_ ?_ ?_
    · refine Derives.negR (A := 𝐅 p) (by simp) ?_
      exact Derives.ax (A := 𝐅 p) (by simp) (by simp)
    · refine Derives.negL (A := 𝐅 p) (by simp) ?_
      refine Derives.evR (A := p) (by simp) ?_
      refine Derives.next
        (show ([] : List (Formula AP)) ⊢ [∼(𝐅 p), 𝐅 p] from ?_) (by simp) (by simp)
      refine Derives.negR (A := 𝐅 p) (by simp) ?_
      exact Derives.ax (A := 𝐅 p) (by simp) (by simp)
    · refine Derives.negR (A := p) (by simp) ?_
      refine Derives.negL (A := 𝐅 p) (by simp) ?_
      refine Derives.evR (A := p) (by simp) ?_
      exact Derives.ax (A := p) (by simp) (by simp)
  · refine Derives.evL (A := p) (I := 𝐆 (p ⇒ 𝐆 q) ⇒ 𝐅 (𝐆 q)) (by simp) ?_ ?_ ?_
    · refine Derives.impR (A := 𝐆 (p ⇒ 𝐆 q)) (B := 𝐅 (𝐆 q)) (by simp) ?_
      refine Derives.alwaysL (A := p ⇒ 𝐆 q) (by simp) ?_
      refine Derives.impL (A := p) (B := 𝐆 q) (by simp) ?_ ?_
      · exact Derives.ax (A := p) (by simp) (by simp)
      · refine Derives.evR (A := 𝐆 q) (by simp) ?_
        exact Derives.ax (A := 𝐆 q) (by simp) (by simp)
    · refine Derives.impR (A := 𝐆 (p ⇒ 𝐆 q)) (B := 𝐅 (𝐆 q)) (by simp) ?_
      refine Derives.alwaysL (A := p ⇒ 𝐆 q) (by simp) ?_
      refine Derives.evR (A := 𝐆 q) (by simp) ?_
      refine Derives.step (Γ' := [𝐆 (p ⇒ 𝐆 q) ⇒ 𝐅 (𝐆 q), 𝐆 (p ⇒ 𝐆 q)])
        (B := 𝐅 (𝐆 q)) ?_ (by simp) (by simp)
      refine Derives.impL (A := 𝐆 (p ⇒ 𝐆 q)) (B := 𝐅 (𝐆 q)) (by simp) ?_ ?_
      · exact Derives.ax (A := 𝐆 (p ⇒ 𝐆 q)) (by simp) (by simp)
      · exact Derives.ax (A := 𝐅 (𝐆 q)) (by simp) (by simp)
    · refine Derives.impL (A := 𝐆 (p ⇒ 𝐆 q)) (B := 𝐅 (𝐆 q)) (by simp) ?_ ?_
      · exact Derives.ax (A := 𝐆 (p ⇒ 𝐆 q)) (by simp) (by simp)
      · exact Derives.ax (A := 𝐅 (𝐆 q)) (by simp) (by simp)

theorem d1_full {AP : Type} (p q : Formula AP) :
    [𝐅 (𝐆 (p ⇒ 𝐆 q))] ⊢ [𝐅 (𝐆 (∼p)) ⋎ 𝐅 (𝐆 q)] := by
  refine Derives.evL (A := 𝐆 (p ⇒ 𝐆 q)) (I := 𝐅 (𝐆 (∼p)) ⋎ 𝐅 (𝐆 q)) (by simp)
    (d1_core p q) ?_ ?_
  · refine Derives.orR (A := 𝐅 (𝐆 (∼p))) (B := 𝐅 (𝐆 q)) (by simp) ?_
    refine Derives.evR (A := 𝐆 (∼p)) (by simp) ?_
    refine Derives.evR (A := 𝐆 q) (by simp) ?_
    refine Derives.next
      (show [𝐅 (𝐆 (∼p)) ⋎ 𝐅 (𝐆 q)] ⊢ [𝐅 (𝐆 (∼p)), 𝐅 (𝐆 q)] from ?_) (by simp) (by simp)
    refine Derives.orL (A := 𝐅 (𝐆 (∼p))) (B := 𝐅 (𝐆 q)) (by simp) ?_ ?_
    · exact Derives.ax (A := 𝐅 (𝐆 (∼p))) (by simp) (by simp)
    · exact Derives.ax (A := 𝐅 (𝐆 q)) (by simp) (by simp)
  · exact Derives.ax (A := 𝐅 (𝐆 (∼p)) ⋎ 𝐅 (𝐆 q)) (by simp) (by simp)

theorem d2_full {AP : Type} (p q : Formula AP) :
    [𝐅 (𝐆 (∼p)) ⋎ 𝐅 (𝐆 q)] ⊢ [𝐅 (𝐆 (p ⇒ 𝐆 q))] := by
  refine Derives.orL (A := 𝐅 (𝐆 (∼p))) (B := 𝐅 (𝐆 q)) (by simp) ?_ ?_
  · refine Derives.evL (A := 𝐆 (∼p)) (I := 𝐅 (𝐆 (p ⇒ 𝐆 q))) (by simp) ?_ ?_ ?_
    · refine Derives.evR (A := 𝐆 (p ⇒ 𝐆 q)) (by simp) ?_
      refine Derives.alwaysR (A := p ⇒ 𝐆 q) (I := 𝐆 (∼p)) (by simp) ?_ ?_ ?_
      · exact Derives.ax (A := 𝐆 (∼p)) (by simp) (by simp)
      · refine Derives.alwaysL (A := ∼p) (by simp) ?_
        exact Derives.ax (A := 𝐗 (𝐆 (∼p))) (by simp) (by simp)
      · refine Derives.impR (A := p) (B := 𝐆 q) (by simp) ?_
        refine Derives.alwaysL (A := ∼p) (by simp) ?_
        refine Derives.negL (A := p) (by simp) ?_
        exact Derives.ax (A := p) (by simp) (by simp)
    · refine Derives.evR (A := 𝐆 (p ⇒ 𝐆 q)) (by simp) ?_
      exact Derives.ax (A := 𝐗 (𝐅 (𝐆 (p ⇒ 𝐆 q)))) (by simp) (by simp)
    · exact Derives.ax (A := 𝐅 (𝐆 (p ⇒ 𝐆 q))) (by simp) (by simp)
  · refine Derives.evL (A := 𝐆 q) (I := 𝐅 (𝐆 (p ⇒ 𝐆 q))) (by simp) ?_ ?_ ?_
    · refine Derives.evR (A := 𝐆 (p ⇒ 𝐆 q)) (by simp) ?_
      refine Derives.alwaysR (A := p ⇒ 𝐆 q) (I := 𝐆 q) (by simp) ?_ ?_ ?_
      · exact Derives.ax (A := 𝐆 q) (by simp) (by simp)
      · refine Derives.alwaysL (A := q) (by simp) ?_
        exact Derives.ax (A := 𝐗 (𝐆 q)) (by simp) (by simp)
      · refine Derives.impR (A := p) (B := 𝐆 q) (by simp) ?_
        exact Derives.ax (A := 𝐆 q) (by simp) (by simp)
    · refine Derives.evR (A := 𝐆 (p ⇒ 𝐆 q)) (by simp) ?_
      exact Derives.ax (A := 𝐗 (𝐅 (𝐆 (p ⇒ 𝐆 q)))) (by simp) (by simp)
    · exact Derives.ax (A := 𝐅 (𝐆 (p ⇒ 𝐆 q))) (by simp) (by simp)

theorem candidate {AP : Type} (p q : Formula AP) :
    ([𝐅 (𝐆 ((p ⇒ 𝐆 (q))))] ⊢ [(𝐅 (𝐆 (∼(p))) ⋎ 𝐅 (𝐆 (q)))]) ∧ ([(𝐅 (𝐆 (∼(p))) ⋎ 𝐅 (𝐆 (q)))] ⊢ [𝐅 (𝐆 ((p ⇒ 𝐆 (q))))]) :=
  ⟨d1_full p q, d2_full p q⟩

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([𝐅 (𝐆 ((p ⇒ 𝐆 (q))))] ⊢ [(𝐅 (𝐆 (∼(p))) ⋎ 𝐅 (𝐆 (q)))]) ∧ ([(𝐅 (𝐆 (∼(p))) ⋎ 𝐅 (𝐆 (q)))] ⊢ [𝐅 (𝐆 ((p ⇒ 𝐆 (q))))]) :=
  Candidate.candidate p q

#print axioms verified
