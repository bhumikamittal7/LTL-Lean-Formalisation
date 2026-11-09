import LTL

open LTL

-- LTL law 254: □ (□ p ⇒ q) ∨ □ (□ q ⇒ p) ≈ ⊤
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem aux_GqI {AP : Type} (p q : Formula AP) :
    [𝐆 q] ⊢ [(𝐆 q) ⋎ (∼(𝐆 ((𝐆 q) ⇒ p)))] :=
  Derives.orR (A := 𝐆 q) (B := ∼(𝐆 ((𝐆 q) ⇒ p))) (by simp)
    (Derives.ax (A := 𝐆 q) (by simp) (by simp))

theorem aux_XI {AP : Type} (p q : Formula AP) {Γ Δ : List (Formula AP)}
    (h : (𝐆 q) ∈ Γ) (h2 : (𝐗 ((𝐆 q) ⋎ (∼(𝐆 ((𝐆 q) ⇒ p))))) ∈ Δ) : Γ ⊢ Δ :=
  Derives.alwaysL (A := q) h
    (Derives.step (aux_GqI p q) (by simp) h2)

theorem aux_inner {AP : Type} (p q : Formula AP) :
    ([] : List (Formula AP)) ⊢ [𝐆 ((𝐆 q) ⇒ p), (𝐆 q) ⋎ (∼(𝐆 ((𝐆 q) ⇒ p)))] :=
  Derives.orR (A := 𝐆 q) (B := ∼(𝐆 ((𝐆 q) ⇒ p))) (by simp)
    (Derives.negR (A := 𝐆 ((𝐆 q) ⇒ p)) (by simp)
      (Derives.ax (A := 𝐆 ((𝐆 q) ⇒ p)) (by simp) (by simp)))

theorem aux_J {AP : Type} (p q : Formula AP) :
    [𝐆 ((𝐆 q) ⇒ p)] ⊢ [((𝐆 q) ⇒ p) ⋏ (𝐗 (𝐆 ((𝐆 q) ⇒ p)))] := by
  refine Derives.alwaysL (A := (𝐆 q) ⇒ p) (by simp) ?_
  exact Derives.andR (A := (𝐆 q) ⇒ p) (B := 𝐗 (𝐆 ((𝐆 q) ⇒ p))) (by simp)
    (Derives.ax (A := (𝐆 q) ⇒ p) (by simp) (by simp))
    (Derives.ax (A := 𝐗 (𝐆 ((𝐆 q) ⇒ p))) (by simp) (by simp))

theorem aux_pres {AP : Type} (p q : Formula AP) :
    [(𝐆 q) ⋎ (∼(𝐆 ((𝐆 q) ⇒ p)))] ⊢ [𝐗 ((𝐆 q) ⋎ (∼(𝐆 ((𝐆 q) ⇒ p))))] := by
  refine Derives.orL (A := 𝐆 q) (B := ∼(𝐆 ((𝐆 q) ⇒ p))) (by simp) ?_ ?_
  · exact aux_XI p q (by simp) (by simp)
  · refine Derives.negL (A := 𝐆 ((𝐆 q) ⇒ p)) (by simp) ?_
    refine Derives.alwaysR (A := (𝐆 q) ⇒ p)
      (((𝐆 q) ⇒ p) ⋏ (𝐗 (𝐆 ((𝐆 q) ⇒ p)))) (by simp) ?_ ?_ ?_
    · refine Derives.andR (A := (𝐆 q) ⇒ p) (B := 𝐗 (𝐆 ((𝐆 q) ⇒ p))) (by simp) ?_ ?_
      · refine Derives.impR (A := 𝐆 q) (B := p) (by simp) ?_
        exact aux_XI p q (by simp) (by simp)
      · exact Derives.next (aux_inner p q) (by simp) (by simp)
    · refine Derives.andL (A := (𝐆 q) ⇒ p) (B := 𝐗 (𝐆 ((𝐆 q) ⇒ p))) (by simp) ?_
      exact Derives.step (aux_J p q) (by simp) (by simp)
    · refine Derives.andL (A := (𝐆 q) ⇒ p) (B := 𝐗 (𝐆 ((𝐆 q) ⇒ p))) (by simp) ?_
      exact Derives.ax (A := (𝐆 q) ⇒ p) (by simp) (by simp)

theorem aux_goal {AP : Type} (p q : Formula AP) :
    [(𝐆 q) ⋎ (∼(𝐆 ((𝐆 q) ⇒ p)))] ⊢ [(𝐆 p) ⇒ q] := by
  refine Derives.impR (A := 𝐆 p) (B := q) (by simp) ?_
  refine Derives.orL (A := 𝐆 q) (B := ∼(𝐆 ((𝐆 q) ⇒ p))) (by simp) ?_ ?_
  · exact Derives.alwaysL (A := q) (by simp) (Derives.ax (A := q) (by simp) (by simp))
  · refine Derives.negL (A := 𝐆 ((𝐆 q) ⇒ p)) (by simp) ?_
    refine Derives.alwaysR (A := (𝐆 q) ⇒ p) (𝐆 p) (by simp)
      (Derives.ax (A := 𝐆 p) (by simp) (by simp)) ?_ ?_
    · exact Derives.alwaysL (A := p) (by simp)
        (Derives.ax (A := 𝐗 (𝐆 p)) (by simp) (by simp))
    · refine Derives.impR (A := 𝐆 q) (B := p) (by simp) ?_
      exact Derives.alwaysL (A := p) (by simp) (Derives.ax (A := p) (by simp) (by simp))

theorem candidate {AP : Type} (p q : Formula AP) :
    ([(𝐆 ((𝐆 (p) ⇒ q)) ⋎ 𝐆 ((𝐆 (q) ⇒ p)))] ⊢ [⊤ₗ]) ∧ ([⊤ₗ] ⊢ [(𝐆 ((𝐆 (p) ⇒ q)) ⋎ 𝐆 ((𝐆 (q) ⇒ p)))]) := by
  refine ⟨Derives.topR (by simp), ?_⟩
  refine Derives.orR (A := 𝐆 ((𝐆 p) ⇒ q)) (B := 𝐆 ((𝐆 q) ⇒ p)) (by simp) ?_
  refine Derives.alwaysR (A := (𝐆 p) ⇒ q) ((𝐆 q) ⋎ (∼(𝐆 ((𝐆 q) ⇒ p)))) (by simp) ?_
    (aux_pres p q) (aux_goal p q)
  refine Derives.orR (A := 𝐆 q) (B := ∼(𝐆 ((𝐆 q) ⇒ p))) (by simp) ?_
  refine Derives.negR (A := 𝐆 ((𝐆 q) ⇒ p)) (by simp) ?_
  exact Derives.ax (A := 𝐆 ((𝐆 q) ⇒ p)) (by simp) (by simp)

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([(𝐆 ((𝐆 (p) ⇒ q)) ⋎ 𝐆 ((𝐆 (q) ⇒ p)))] ⊢ [⊤ₗ]) ∧ ([⊤ₗ] ⊢ [(𝐆 ((𝐆 (p) ⇒ q)) ⋎ 𝐆 ((𝐆 (q) ⇒ p)))]) :=
  Candidate.candidate p q

#print axioms verified
