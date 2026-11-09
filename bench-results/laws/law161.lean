import LTL

open LTL

-- LTL law 161: □ ◇ (p ∨ q) ≈ □ ◇ p ∨ □ ◇ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem hXGF {AP : Type} (A : Formula AP) :
    [𝐗 (𝐆 (𝐅 A))] ⊢ [𝐆 (𝐅 A)] := by
  refine .alwaysR (A := 𝐅 A) (𝐗 (𝐆 (𝐅 A))) (by simp) ?_ ?_ ?_
  · exact .ax (A := 𝐗 (𝐆 (𝐅 A))) (by simp) (by simp)
  · have h : [𝐆 (𝐅 A)] ⊢ [𝐗 (𝐆 (𝐅 A))] :=
      .alwaysL (A := 𝐅 A) (by simp) (.ax (A := 𝐗 (𝐆 (𝐅 A))) (by simp) (by simp))
    exact .step h (by simp) (by simp)
  · refine .evR (A := A) (by simp) ?_
    have h : [𝐆 (𝐅 A)] ⊢ [𝐅 A] :=
      .alwaysL (A := 𝐅 A) (by simp) (.ax (A := 𝐅 A) (by simp) (by simp))
    exact .step h (by simp) (by simp)

theorem hNotGF {AP : Type} (A : Formula AP) :
    [∼ (𝐆 (𝐅 A))] ⊢ [𝐗 (∼ (𝐆 (𝐅 A)))] := by
  refine .negL (A := 𝐆 (𝐅 A)) (by simp) ?_
  refine .cut (𝐗 (𝐆 (𝐅 A))) ?_ ?_
  · have h : ([] : List (Formula AP)) ⊢ [𝐆 (𝐅 A), ∼ (𝐆 (𝐅 A))] :=
      .negR (A := 𝐆 (𝐅 A)) (by simp) (.ax (A := 𝐆 (𝐅 A)) (by simp) (by simp))
    exact .next h (by simp) (by simp)
  · exact .wk (hXGF A) (by simp) (by simp)

theorem hNotF {AP : Type} (A : Formula AP) :
    [∼ (𝐅 A)] ⊢ [𝐗 (∼ (𝐅 A))] := by
  refine .negL (A := 𝐅 A) (by simp) ?_
  refine .evR (A := A) (by simp) ?_
  have h : ([] : List (Formula AP)) ⊢ [𝐅 A, ∼ (𝐅 A)] :=
    .negR (A := 𝐅 A) (by simp) (.ax (A := 𝐅 A) (by simp) (by simp))
  exact .next h (by simp) (by simp)

theorem hOrF {AP : Type} (p q : Formula AP) :
    [p ⋎ q] ⊢ [(𝐅 p) ⋎ (𝐅 q)] := by
  refine .orR (A := 𝐅 p) (B := 𝐅 q) (by simp) ?_
  refine .orL (A := p) (B := q) (by simp) ?_ ?_
  · exact .evR (A := p) (by simp) (.ax (A := p) (by simp) (by simp))
  · exact .evR (A := q) (by simp) (.ax (A := q) (by simp) (by simp))

theorem hXOrF {AP : Type} (p q : Formula AP) :
    [𝐗 ((𝐅 p) ⋎ (𝐅 q))] ⊢ [(𝐅 p) ⋎ (𝐅 q)] := by
  refine .orR (A := 𝐅 p) (B := 𝐅 q) (by simp) ?_
  refine .evR (A := p) (by simp) ?_
  refine .evR (A := q) (by simp) ?_
  have h : [(𝐅 p) ⋎ (𝐅 q)] ⊢ [𝐅 p, 𝐅 q] :=
    .orL (A := 𝐅 p) (B := 𝐅 q) (by simp) (.ax (A := 𝐅 p) (by simp) (by simp))
      (.ax (A := 𝐅 q) (by simp) (by simp))
  exact .next h (by simp) (by simp)

theorem hInv {AP : Type} (X Y : Formula AP) (hY : [Y] ⊢ [𝐗 Y]) :
    [(𝐆 X) ⋏ Y] ⊢ [𝐗 ((𝐆 X) ⋏ Y)] := by
  refine .andL (A := 𝐆 X) (B := Y) (by simp) ?_
  refine .alwaysL (A := X) (by simp) ?_
  refine .cut (𝐗 Y) (.wk hY (by simp) (by simp)) ?_
  have h : [𝐆 X, Y] ⊢ [(𝐆 X) ⋏ Y] :=
    .andR (A := 𝐆 X) (B := Y) (by simp) (.ax (A := 𝐆 X) (by simp) (by simp))
      (.ax (A := Y) (by simp) (by simp))
  exact .step h (by simp) (by simp)

theorem hJ {AP : Type} (p q : Formula AP) :
    [(𝐆 (𝐅 (p ⋎ q))) ⋏ (∼ (𝐅 p))] ⊢ [𝐅 q] := by
  refine .andL (A := 𝐆 (𝐅 (p ⋎ q))) (B := ∼ (𝐅 p)) (by simp) ?_
  refine .alwaysL (A := 𝐅 (p ⋎ q)) (by simp) ?_
  refine .evL (A := p ⋎ q) ((𝐅 p) ⋎ (𝐅 q)) (by simp) (hOrF p q) (hXOrF p q) ?_
  refine .orL (A := 𝐅 p) (B := 𝐅 q) (by simp) ?_ ?_
  · exact .negL (A := 𝐅 p) (by simp) (.ax (A := 𝐅 p) (by simp) (by simp))
  · exact .ax (A := 𝐅 q) (by simp) (by simp)

theorem dir1 {AP : Type} (p q : Formula AP) :
    [𝐆 (𝐅 ((p ⋎ q)))] ⊢ [(𝐆 (𝐅 (p)) ⋎ 𝐆 (𝐅 (q)))] := by
  refine .orR (A := 𝐆 (𝐅 p)) (B := 𝐆 (𝐅 q)) (by simp) ?_
  refine .alwaysR (A := 𝐅 p) ((𝐆 (𝐅 (p ⋎ q))) ⋏ (∼ (𝐆 (𝐅 q)))) (by simp) ?_ ?_ ?_
  · refine .andR (A := 𝐆 (𝐅 (p ⋎ q))) (B := ∼ (𝐆 (𝐅 q))) (by simp) ?_ ?_
    · exact .ax (A := 𝐆 (𝐅 (p ⋎ q))) (by simp) (by simp)
    · exact .negR (A := 𝐆 (𝐅 q)) (by simp) (.ax (A := 𝐆 (𝐅 q)) (by simp) (by simp))
  · exact hInv (𝐅 (p ⋎ q)) (∼ (𝐆 (𝐅 q))) (hNotGF q)
  · refine .andL (A := 𝐆 (𝐅 (p ⋎ q))) (B := ∼ (𝐆 (𝐅 q))) (by simp) ?_
    refine .negL (A := 𝐆 (𝐅 q)) (by simp) ?_
    refine .alwaysR (A := 𝐅 q) ((𝐆 (𝐅 (p ⋎ q))) ⋏ (∼ (𝐅 p))) (by simp) ?_ ?_ ?_
    · refine .andR (A := 𝐆 (𝐅 (p ⋎ q))) (B := ∼ (𝐅 p)) (by simp) ?_ ?_
      · exact .ax (A := 𝐆 (𝐅 (p ⋎ q))) (by simp) (by simp)
      · exact .negR (A := 𝐅 p) (by simp) (.ax (A := 𝐅 p) (by simp) (by simp))
    · exact hInv (𝐅 (p ⋎ q)) (∼ (𝐅 p)) (hNotF p)
    · exact hJ p q

theorem hFl {AP : Type} (p q : Formula AP) :
    [𝐅 p] ⊢ [𝐅 (p ⋎ q)] := by
  refine .evL (A := p) (𝐅 (p ⋎ q)) (by simp) ?_ ?_ ?_
  · refine .evR (A := p ⋎ q) (by simp) ?_
    exact .orR (A := p) (B := q) (by simp) (.ax (A := p) (by simp) (by simp))
  · exact .evR (A := p ⋎ q) (by simp) (.ax (A := 𝐗 (𝐅 (p ⋎ q))) (by simp) (by simp))
  · exact .ax (A := 𝐅 (p ⋎ q)) (by simp) (by simp)

theorem hFr {AP : Type} (p q : Formula AP) :
    [𝐅 q] ⊢ [𝐅 (p ⋎ q)] := by
  refine .evL (A := q) (𝐅 (p ⋎ q)) (by simp) ?_ ?_ ?_
  · refine .evR (A := p ⋎ q) (by simp) ?_
    exact .orR (A := p) (B := q) (by simp) (.ax (A := q) (by simp) (by simp))
  · exact .evR (A := p ⋎ q) (by simp) (.ax (A := 𝐗 (𝐅 (p ⋎ q))) (by simp) (by simp))
  · exact .ax (A := 𝐅 (p ⋎ q)) (by simp) (by simp)

theorem hGFl {AP : Type} (p q : Formula AP) :
    [𝐆 (𝐅 p)] ⊢ [𝐆 (𝐅 (p ⋎ q))] := by
  refine .alwaysR (A := 𝐅 (p ⋎ q)) (𝐆 (𝐅 p)) (by simp) ?_ ?_ ?_
  · exact .ax (A := 𝐆 (𝐅 p)) (by simp) (by simp)
  · exact .alwaysL (A := 𝐅 p) (by simp) (.ax (A := 𝐗 (𝐆 (𝐅 p))) (by simp) (by simp))
  · exact .alwaysL (A := 𝐅 p) (by simp) (.wk (hFl p q) (by simp) (by simp))

theorem hGFr {AP : Type} (p q : Formula AP) :
    [𝐆 (𝐅 q)] ⊢ [𝐆 (𝐅 (p ⋎ q))] := by
  refine .alwaysR (A := 𝐅 (p ⋎ q)) (𝐆 (𝐅 q)) (by simp) ?_ ?_ ?_
  · exact .ax (A := 𝐆 (𝐅 q)) (by simp) (by simp)
  · exact .alwaysL (A := 𝐅 q) (by simp) (.ax (A := 𝐗 (𝐆 (𝐅 q))) (by simp) (by simp))
  · exact .alwaysL (A := 𝐅 q) (by simp) (.wk (hFr p q) (by simp) (by simp))

theorem dir2 {AP : Type} (p q : Formula AP) :
    [(𝐆 (𝐅 (p)) ⋎ 𝐆 (𝐅 (q)))] ⊢ [𝐆 (𝐅 ((p ⋎ q)))] := by
  refine .orL (A := 𝐆 (𝐅 p)) (B := 𝐆 (𝐅 q)) (by simp) ?_ ?_
  · exact .wk (hGFl p q) (by simp) (by simp)
  · exact .wk (hGFr p q) (by simp) (by simp)

theorem candidate {AP : Type} (p q : Formula AP) :
    ([𝐆 (𝐅 ((p ⋎ q)))] ⊢ [(𝐆 (𝐅 (p)) ⋎ 𝐆 (𝐅 (q)))]) ∧ ([(𝐆 (𝐅 (p)) ⋎ 𝐆 (𝐅 (q)))] ⊢ [𝐆 (𝐅 ((p ⋎ q)))]) :=
  ⟨dir1 p q, dir2 p q⟩

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([𝐆 (𝐅 ((p ⋎ q)))] ⊢ [(𝐆 (𝐅 (p)) ⋎ 𝐆 (𝐅 (q)))]) ∧ ([(𝐆 (𝐅 (p)) ⋎ 𝐆 (𝐅 (q)))] ⊢ [𝐆 (𝐅 ((p ⋎ q)))]) :=
  Candidate.candidate p q

#print axioms verified
