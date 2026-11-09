import LTL

open LTL

-- LTL law 165: □ ((p ∨ □ q) ∧ (□ p ∨ q)) ≈ □ p ∨ □ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem d1_pres {AP : Type} (p q : Formula AP) :
    [((𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q)) ⋏ (∼(𝐆 p))) ⋎ 𝐆 q)] ⊢
      [𝐗 ((𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q)) ⋏ (∼(𝐆 p))) ⋎ 𝐆 q)] := by
  refine Derives.orL (A := (𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q)) ⋏ (∼(𝐆 p)))) (B := 𝐆 q) (by simp) ?_ ?_
  · refine Derives.andL (A := 𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q))) (B := ∼(𝐆 p)) (by simp) ?_
    refine Derives.alwaysL (A := ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q))) (by simp) ?_
    refine Derives.andL (A := (p ⋎ 𝐆 q)) (B := (𝐆 p ⋎ q)) (by simp) ?_
    refine Derives.orL (A := p) (B := 𝐆 q) (by simp) ?_ ?_
    · refine Derives.negL (A := 𝐆 p) (by simp) ?_
      refine Derives.alwaysR (A := p) (I := p ⋏ 𝐗 (𝐆 p)) (by simp) ?_ ?_ ?_
      · refine Derives.andR (A := p) (B := 𝐗 (𝐆 p)) (by simp) ?_ ?_
        · exact Derives.ax (A := p) (by simp) (by simp)
        · refine Derives.next
            (show [𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q))] ⊢
              [𝐆 p, ((𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q)) ⋏ (∼(𝐆 p))) ⋎ 𝐆 q)] from ?_)
            (by simp) (by simp)
          refine Derives.orR (A := (𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q)) ⋏ (∼(𝐆 p)))) (B := 𝐆 q) (by simp) ?_
          refine Derives.andR (A := 𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q))) (B := ∼(𝐆 p)) (by simp) ?_ ?_
          · exact Derives.ax (A := 𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q))) (by simp) (by simp)
          · refine Derives.negR (A := 𝐆 p) (by simp) ?_
            exact Derives.ax (A := 𝐆 p) (by simp) (by simp)
      · refine Derives.andL (A := p) (B := 𝐗 (𝐆 p)) (by simp) ?_
        refine Derives.step (Γ' := [𝐆 p]) (show [𝐆 p] ⊢ [p ⋏ 𝐗 (𝐆 p)] from ?_) (by simp) (by simp)
        refine Derives.alwaysL (A := p) (by simp) ?_
        refine Derives.andR (A := p) (B := 𝐗 (𝐆 p)) (by simp) ?_ ?_
        · exact Derives.ax (A := p) (by simp) (by simp)
        · exact Derives.ax (A := 𝐗 (𝐆 p)) (by simp) (by simp)
      · refine Derives.andL (A := p) (B := 𝐗 (𝐆 p)) (by simp) ?_
        exact Derives.ax (A := p) (by simp) (by simp)
    · refine Derives.alwaysL (A := q) (by simp) ?_
      refine Derives.step (Γ' := [𝐆 q])
        (show [𝐆 q] ⊢ [((𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q)) ⋏ (∼(𝐆 p))) ⋎ 𝐆 q)] from ?_) (by simp) (by simp)
      refine Derives.orR (A := (𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q)) ⋏ (∼(𝐆 p)))) (B := 𝐆 q) (by simp) ?_
      exact Derives.ax (A := 𝐆 q) (by simp) (by simp)
  · refine Derives.alwaysL (A := q) (by simp) ?_
    refine Derives.step (Γ' := [𝐆 q])
      (show [𝐆 q] ⊢ [((𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q)) ⋏ (∼(𝐆 p))) ⋎ 𝐆 q)] from ?_) (by simp) (by simp)
    refine Derives.orR (A := (𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q)) ⋏ (∼(𝐆 p)))) (B := 𝐆 q) (by simp) ?_
    exact Derives.ax (A := 𝐆 q) (by simp) (by simp)

theorem d1_goal {AP : Type} (p q : Formula AP) :
    [((𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q)) ⋏ (∼(𝐆 p))) ⋎ 𝐆 q)] ⊢ [q] := by
  refine Derives.orL (A := (𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q)) ⋏ (∼(𝐆 p)))) (B := 𝐆 q) (by simp) ?_ ?_
  · refine Derives.andL (A := 𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q))) (B := ∼(𝐆 p)) (by simp) ?_
    refine Derives.alwaysL (A := ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q))) (by simp) ?_
    refine Derives.andL (A := (p ⋎ 𝐆 q)) (B := (𝐆 p ⋎ q)) (by simp) ?_
    refine Derives.orL (A := 𝐆 p) (B := q) (by simp) ?_ ?_
    · refine Derives.negL (A := 𝐆 p) (by simp) ?_
      exact Derives.ax (A := 𝐆 p) (by simp) (by simp)
    · exact Derives.ax (A := q) (by simp) (by simp)
  · refine Derives.alwaysL (A := q) (by simp) ?_
    exact Derives.ax (A := q) (by simp) (by simp)

theorem d1 {AP : Type} (p q : Formula AP) :
    [𝐆 (((p ⋎ 𝐆 (q)) ⋏ (𝐆 (p) ⋎ q)))] ⊢ [(𝐆 (p) ⋎ 𝐆 (q))] := by
  refine Derives.orR (A := 𝐆 p) (B := 𝐆 q) (by simp) ?_
  refine Derives.alwaysR (A := q)
    (I := ((𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q)) ⋏ (∼(𝐆 p))) ⋎ 𝐆 q)) (by simp) ?_ (d1_pres p q) (d1_goal p q)
  refine Derives.orR (A := (𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q)) ⋏ (∼(𝐆 p)))) (B := 𝐆 q) (by simp) ?_
  refine Derives.andR (A := 𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q))) (B := ∼(𝐆 p)) (by simp) ?_ ?_
  · exact Derives.ax (A := 𝐆 ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q))) (by simp) (by simp)
  · refine Derives.negR (A := 𝐆 p) (by simp) ?_
    exact Derives.ax (A := 𝐆 p) (by simp) (by simp)

theorem d2 {AP : Type} (p q : Formula AP) :
    [(𝐆 (p) ⋎ 𝐆 (q))] ⊢ [𝐆 (((p ⋎ 𝐆 (q)) ⋏ (𝐆 (p) ⋎ q)))] := by
  refine Derives.orL (A := 𝐆 p) (B := 𝐆 q) (by simp) ?_ ?_
  · refine Derives.alwaysR (A := ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q))) (I := 𝐆 p) (by simp) ?_ ?_ ?_
    · exact Derives.ax (A := 𝐆 p) (by simp) (by simp)
    · refine Derives.alwaysL (A := p) (by simp) ?_
      exact Derives.ax (A := 𝐗 (𝐆 p)) (by simp) (by simp)
    · refine Derives.andR (A := p ⋎ 𝐆 q) (B := 𝐆 p ⋎ q) (by simp) ?_ ?_
      · refine Derives.orR (A := p) (B := 𝐆 q) (by simp) ?_
        refine Derives.alwaysL (A := p) (by simp) ?_
        exact Derives.ax (A := p) (by simp) (by simp)
      · refine Derives.orR (A := 𝐆 p) (B := q) (by simp) ?_
        exact Derives.ax (A := 𝐆 p) (by simp) (by simp)
  · refine Derives.alwaysR (A := ((p ⋎ 𝐆 q) ⋏ (𝐆 p ⋎ q))) (I := 𝐆 q) (by simp) ?_ ?_ ?_
    · exact Derives.ax (A := 𝐆 q) (by simp) (by simp)
    · refine Derives.alwaysL (A := q) (by simp) ?_
      exact Derives.ax (A := 𝐗 (𝐆 q)) (by simp) (by simp)
    · refine Derives.andR (A := p ⋎ 𝐆 q) (B := 𝐆 p ⋎ q) (by simp) ?_ ?_
      · refine Derives.orR (A := p) (B := 𝐆 q) (by simp) ?_
        exact Derives.ax (A := 𝐆 q) (by simp) (by simp)
      · refine Derives.orR (A := 𝐆 p) (B := q) (by simp) ?_
        refine Derives.alwaysL (A := q) (by simp) ?_
        exact Derives.ax (A := q) (by simp) (by simp)

theorem candidate {AP : Type} (p q : Formula AP) :
    ([𝐆 (((p ⋎ 𝐆 (q)) ⋏ (𝐆 (p) ⋎ q)))] ⊢ [(𝐆 (p) ⋎ 𝐆 (q))]) ∧ ([(𝐆 (p) ⋎ 𝐆 (q))] ⊢ [𝐆 (((p ⋎ 𝐆 (q)) ⋏ (𝐆 (p) ⋎ q)))]) :=
  ⟨d1 p q, d2 p q⟩

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([𝐆 (((p ⋎ 𝐆 (q)) ⋏ (𝐆 (p) ⋎ q)))] ⊢ [(𝐆 (p) ⋎ 𝐆 (q))]) ∧ ([(𝐆 (p) ⋎ 𝐆 (q))] ⊢ [𝐆 (((p ⋎ 𝐆 (q)) ⋏ (𝐆 (p) ⋎ q)))]) :=
  Candidate.candidate p q

#print axioms verified
