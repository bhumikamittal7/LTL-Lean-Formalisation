import LTL

open LTL

-- LTL law 164: □ (□ ◇ p ⇒ ◇ q) ≈ ◇ □ ¬p ∨ □ ◇ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem negF_next_h {AP : Type} (A : Formula AP) :
    [∼(𝐅 A)] ⊢ [𝐗 (∼(𝐅 A))] :=
  Derives.negL (A := 𝐅 A) (by simp) <|
  Derives.evR (A := A) (by simp) <|
  Derives.next (Γ' := []) (Δ' := [𝐅 A, ∼(𝐅 A)])
    (Derives.negR (A := 𝐅 A) (by simp) (Derives.ax (A := 𝐅 A) (by simp) (by simp)))
    (by simp) (by simp)

theorem negFG_F_h {AP : Type} (A : Formula AP) :
    [∼(𝐅 (𝐆 (∼A)))] ⊢ [𝐅 A] :=
  Derives.negL (A := 𝐅 (𝐆 (∼A))) (by simp) <|
  Derives.evR (A := 𝐆 (∼A)) (by simp) <|
  Derives.alwaysR (∼(𝐅 A)) (A := ∼A) (by simp)
    (Derives.negR (A := 𝐅 A) (by simp) (Derives.ax (A := 𝐅 A) (by simp) (by simp)))
    (negF_next_h A)
    (Derives.negR (A := A) (by simp) <|
      Derives.negL (A := 𝐅 A) (by simp) <|
      Derives.evR (A := A) (by simp) <|
      Derives.ax (A := A) (by simp) (by simp))

theorem FG_next_h {AP : Type} (A : Formula AP) :
    [𝐅 (𝐆 A)] ⊢ [𝐗 (𝐅 (𝐆 A))] :=
  Derives.evL (𝐗 (𝐅 (𝐆 A))) (A := 𝐆 A) (by simp)
    (Derives.alwaysL (A := A) (by simp) <|
      Derives.step (Γ' := [𝐆 A]) (B := 𝐅 (𝐆 A))
        (Derives.evR (A := 𝐆 A) (by simp) (Derives.ax (A := 𝐆 A) (by simp) (by simp)))
        (by simp) (by simp))
    (Derives.step (Γ' := [𝐗 (𝐅 (𝐆 A))]) (B := 𝐅 (𝐆 A))
      (Derives.evR (A := 𝐆 A) (by simp)
        (Derives.ax (A := 𝐗 (𝐅 (𝐆 A))) (by simp) (by simp)))
      (by simp) (by simp))
    (Derives.ax (A := 𝐗 (𝐅 (𝐆 A))) (by simp) (by simp))

theorem contra_h {AP : Type} (A : Formula AP) :
    [𝐆 (𝐅 A), 𝐅 (𝐆 (∼A))] ⊢ [] :=
  Derives.evL (∼(𝐆 (𝐅 A))) (A := 𝐆 (∼A)) (by simp)
    (Derives.negR (A := 𝐆 (𝐅 A)) (by simp) <|
      Derives.alwaysL (A := 𝐅 A) (by simp) <|
      Derives.evL (∼(𝐆 (∼A))) (A := A) (by simp)
        (Derives.negR (A := 𝐆 (∼A)) (by simp) <|
          Derives.alwaysL (A := ∼A) (by simp) <|
          Derives.negL (A := A) (by simp) <|
          Derives.ax (A := A) (by simp) (by simp))
        (Derives.negR (A := 𝐆 (∼A)) (by simp) <|
          Derives.alwaysL (A := ∼A) (by simp) <|
          Derives.next (Γ' := [𝐆 (∼A), ∼(𝐆 (∼A))]) (Δ' := [])
            (Derives.negL (A := 𝐆 (∼A)) (by simp)
              (Derives.ax (A := 𝐆 (∼A)) (by simp) (by simp)))
            (by simp) (by simp))
        (Derives.negL (A := 𝐆 (∼A)) (by simp)
          (Derives.ax (A := 𝐆 (∼A)) (by simp) (by simp))))
    (Derives.negR (A := 𝐆 (𝐅 A)) (by simp) <|
      Derives.alwaysL (A := 𝐅 A) (by simp) <|
      Derives.next (Γ' := [𝐆 (𝐅 A), ∼(𝐆 (𝐅 A))]) (Δ' := [])
        (Derives.negL (A := 𝐆 (𝐅 A)) (by simp)
          (Derives.ax (A := 𝐆 (𝐅 A)) (by simp) (by simp)))
        (by simp) (by simp))
    (Derives.negL (A := 𝐆 (𝐅 A)) (by simp)
      (Derives.ax (A := 𝐆 (𝐅 A)) (by simp) (by simp)))

theorem candidate {AP : Type} (p q : Formula AP) :
    ([𝐆 ((𝐆 (𝐅 (p)) ⇒ 𝐅 (q)))] ⊢ [(𝐅 (𝐆 (∼(p))) ⋎ 𝐆 (𝐅 (q)))]) ∧ ([(𝐅 (𝐆 (∼(p))) ⋎ 𝐆 (𝐅 (q)))] ⊢ [𝐆 ((𝐆 (𝐅 (p)) ⇒ 𝐅 (q)))]) := by
  refine ⟨?_, ?_⟩
  · exact
      Derives.orR (A := 𝐅 (𝐆 (∼p))) (B := 𝐆 (𝐅 q)) (by simp) <|
      Derives.cut (𝐆 (𝐅 p))
        (Derives.alwaysR (∼(𝐅 (𝐆 (∼p)))) (A := 𝐅 p) (by simp)
          (Derives.negR (A := 𝐅 (𝐆 (∼p))) (by simp)
            (Derives.ax (A := 𝐅 (𝐆 (∼p))) (by simp) (by simp)))
          (negF_next_h (𝐆 (∼p)))
          (negFG_F_h p))
        (Derives.alwaysR (𝐆 (𝐅 p) ⋏ 𝐆 ((𝐆 (𝐅 p) ⇒ 𝐅 q))) (A := 𝐅 q) (by simp)
          (Derives.andR (A := 𝐆 (𝐅 p)) (B := 𝐆 ((𝐆 (𝐅 p) ⇒ 𝐅 q))) (by simp)
            (Derives.ax (A := 𝐆 (𝐅 p)) (by simp) (by simp))
            (Derives.ax (A := 𝐆 ((𝐆 (𝐅 p) ⇒ 𝐅 q))) (by simp) (by simp)))
          (Derives.andL (A := 𝐆 (𝐅 p)) (B := 𝐆 ((𝐆 (𝐅 p) ⇒ 𝐅 q))) (by simp) <|
            Derives.alwaysL (A := 𝐅 p) (by simp) <|
            Derives.alwaysL (A := (𝐆 (𝐅 p) ⇒ 𝐅 q)) (by simp) <|
            Derives.step (Γ' := [𝐆 (𝐅 p), 𝐆 ((𝐆 (𝐅 p) ⇒ 𝐅 q))])
              (B := 𝐆 (𝐅 p) ⋏ 𝐆 ((𝐆 (𝐅 p) ⇒ 𝐅 q)))
              (Derives.andR (A := 𝐆 (𝐅 p)) (B := 𝐆 ((𝐆 (𝐅 p) ⇒ 𝐅 q))) (by simp)
                (Derives.ax (A := 𝐆 (𝐅 p)) (by simp) (by simp))
                (Derives.ax (A := 𝐆 ((𝐆 (𝐅 p) ⇒ 𝐅 q))) (by simp) (by simp)))
              (by simp) (by simp))
          (Derives.andL (A := 𝐆 (𝐅 p)) (B := 𝐆 ((𝐆 (𝐅 p) ⇒ 𝐅 q))) (by simp) <|
            Derives.alwaysL (A := (𝐆 (𝐅 p) ⇒ 𝐅 q)) (by simp) <|
            Derives.impL (A := 𝐆 (𝐅 p)) (B := 𝐅 q) (by simp)
              (Derives.ax (A := 𝐆 (𝐅 p)) (by simp) (by simp))
              (Derives.ax (A := 𝐅 q) (by simp) (by simp))))
  · exact
      Derives.orL (A := 𝐅 (𝐆 (∼p))) (B := 𝐆 (𝐅 q)) (by simp)
        (Derives.alwaysR (𝐅 (𝐆 (∼p))) (A := (𝐆 (𝐅 p) ⇒ 𝐅 q)) (by simp)
          (Derives.ax (A := 𝐅 (𝐆 (∼p))) (by simp) (by simp))
          (FG_next_h (∼p))
          (Derives.impR (A := 𝐆 (𝐅 p)) (B := 𝐅 q) (by simp)
            (Derives.wk (contra_h p) (by simp) (by simp))))
        (Derives.alwaysR (𝐆 (𝐅 q)) (A := (𝐆 (𝐅 p) ⇒ 𝐅 q)) (by simp)
          (Derives.ax (A := 𝐆 (𝐅 q)) (by simp) (by simp))
          (Derives.alwaysL (A := 𝐅 q) (by simp)
            (Derives.ax (A := 𝐗 (𝐆 (𝐅 q))) (by simp) (by simp)))
          (Derives.impR (A := 𝐆 (𝐅 p)) (B := 𝐅 q) (by simp) <|
            Derives.alwaysL (A := 𝐅 q) (by simp) <|
            Derives.ax (A := 𝐅 q) (by simp) (by simp)))

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([𝐆 ((𝐆 (𝐅 (p)) ⇒ 𝐅 (q)))] ⊢ [(𝐅 (𝐆 (∼(p))) ⋎ 𝐆 (𝐅 (q)))]) ∧ ([(𝐅 (𝐆 (∼(p))) ⋎ 𝐆 (𝐅 (q)))] ⊢ [𝐆 ((𝐆 (𝐅 (p)) ⇒ 𝐅 (q)))]) :=
  Candidate.candidate p q

#print axioms verified
