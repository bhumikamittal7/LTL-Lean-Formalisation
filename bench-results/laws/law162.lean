import LTL

open LTL

-- LTL law 162: ◇ □ (p ∧ q) ≈ ◇ □ p ∧ ◇ □ q
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem fg_mono {AP : Type} (X Y : Formula AP) (h : [X] ⊢ [Y]) :
    [𝐅 (𝐆 X)] ⊢ [𝐅 (𝐆 Y)] :=
  .evL (A := 𝐆 X) (I := 𝐅 (𝐆 Y)) (by simp)
    (.evR (A := 𝐆 Y) (by simp)
      (.alwaysR (A := Y) (I := 𝐆 X) (by simp)
        (.ax (A := 𝐆 X) (by simp) (by simp))
        (.alwaysL (A := X) (by simp) (.ax (A := 𝐗 (𝐆 X)) (by simp) (by simp)))
        (.alwaysL (A := X) (by simp) (.wk h (by simp) (by simp)))))
    (.evR (A := 𝐆 Y) (by simp) (.ax (A := 𝐗 (𝐅 (𝐆 Y))) (by simp) (by simp)))
    (.ax (A := 𝐅 (𝐆 Y)) (by simp) (by simp))

theorem xfg {AP : Type} (q : Formula AP) :
    [𝐅 (𝐆 q)] ⊢ [𝐗 (𝐅 (𝐆 q))] :=
  .evL (A := 𝐆 q) (I := 𝐗 (𝐅 (𝐆 q))) (by simp)
    (.alwaysL (A := q) (by simp)
      (.step (Γ' := [𝐆 q])
        (show [𝐆 q] ⊢ [𝐅 (𝐆 q)] from
          .evR (A := 𝐆 q) (by simp) (.ax (A := 𝐆 q) (by simp) (by simp)))
        (by simp) (by simp)))
    (.step (Γ' := [𝐗 (𝐅 (𝐆 q))])
      (show [𝐗 (𝐅 (𝐆 q))] ⊢ [𝐅 (𝐆 q)] from
        .evR (A := 𝐆 q) (by simp) (.ax (A := 𝐗 (𝐅 (𝐆 q))) (by simp) (by simp)))
      (by simp) (by simp))
    (.ax (A := 𝐗 (𝐅 (𝐆 q))) (by simp) (by simp))

theorem g_and {AP : Type} (p q : Formula AP) :
    [𝐆 p, 𝐆 q] ⊢ [𝐆 (p ⋏ q)] :=
  .alwaysR (A := p ⋏ q) (I := (𝐆 p) ⋏ (𝐆 q)) (by simp)
    (.andR (A := 𝐆 p) (B := 𝐆 q) (by simp)
      (.ax (A := 𝐆 p) (by simp) (by simp))
      (.ax (A := 𝐆 q) (by simp) (by simp)))
    (.andL (A := 𝐆 p) (B := 𝐆 q) (by simp)
      (.alwaysL (A := p) (by simp) (.alwaysL (A := q) (by simp)
        (.step (Γ' := [𝐆 p, 𝐆 q])
          (show [𝐆 p, 𝐆 q] ⊢ [(𝐆 p) ⋏ (𝐆 q)] from
            .andR (A := 𝐆 p) (B := 𝐆 q) (by simp)
              (.ax (A := 𝐆 p) (by simp) (by simp))
              (.ax (A := 𝐆 q) (by simp) (by simp)))
          (by simp) (by simp)))))
    (.andL (A := 𝐆 p) (B := 𝐆 q) (by simp)
      (.alwaysL (A := p) (by simp) (.alwaysL (A := q) (by simp)
        (.andR (A := p) (B := q) (by simp)
          (.ax (A := p) (by simp) (by simp))
          (.ax (A := q) (by simp) (by simp))))))

theorem g_fg {AP : Type} (p q : Formula AP) :
    [𝐆 p, 𝐆 q] ⊢ [𝐅 (𝐆 (p ⋏ q))] :=
  .evR (A := 𝐆 (p ⋏ q)) (by simp) (.wk (g_and p q) (by simp) (by simp))

theorem fg_base {AP : Type} (p q : Formula AP) :
    [𝐆 p] ⊢ [(𝐅 (𝐆 q)) ⇒ (𝐅 (𝐆 (p ⋏ q)))] :=
  .impR (A := 𝐅 (𝐆 q)) (B := 𝐅 (𝐆 (p ⋏ q))) (by simp)
    (.evL (A := 𝐆 q) (I := (𝐆 p) ⇒ (𝐅 (𝐆 (p ⋏ q)))) (by simp)
      (.impR (A := 𝐆 p) (B := 𝐅 (𝐆 (p ⋏ q))) (by simp)
        (.wk (g_fg p q) (by simp) (by simp)))
      (.impR (A := 𝐆 p) (B := 𝐅 (𝐆 (p ⋏ q))) (by simp)
        (.evR (A := 𝐆 (p ⋏ q)) (by simp)
          (.alwaysL (A := p) (by simp)
            (.step (Γ' := [(𝐆 p) ⇒ (𝐅 (𝐆 (p ⋏ q))), 𝐆 p])
              (show [(𝐆 p) ⇒ (𝐅 (𝐆 (p ⋏ q))), 𝐆 p] ⊢ [𝐅 (𝐆 (p ⋏ q))] from
                .impL (A := 𝐆 p) (B := 𝐅 (𝐆 (p ⋏ q))) (by simp)
                  (.ax (A := 𝐆 p) (by simp) (by simp))
                  (.ax (A := 𝐅 (𝐆 (p ⋏ q))) (by simp) (by simp)))
              (by simp) (by simp)))))
      (.impL (A := 𝐆 p) (B := 𝐅 (𝐆 (p ⋏ q))) (by simp)
        (.ax (A := 𝐆 p) (by simp) (by simp))
        (.ax (A := 𝐅 (𝐆 (p ⋏ q))) (by simp) (by simp))))

theorem fg_stepI {AP : Type} (p q : Formula AP) :
    [𝐗 ((𝐅 (𝐆 q)) ⇒ (𝐅 (𝐆 (p ⋏ q))))] ⊢ [(𝐅 (𝐆 q)) ⇒ (𝐅 (𝐆 (p ⋏ q)))] :=
  .impR (A := 𝐅 (𝐆 q)) (B := 𝐅 (𝐆 (p ⋏ q))) (by simp)
    (.evR (A := 𝐆 (p ⋏ q)) (by simp)
      (.cut (A := 𝐗 (𝐅 (𝐆 q)))
        (.wk (xfg q) (by simp) (by simp))
        (.step (Γ' := [(𝐅 (𝐆 q)) ⇒ (𝐅 (𝐆 (p ⋏ q))), 𝐅 (𝐆 q)])
          (show [(𝐅 (𝐆 q)) ⇒ (𝐅 (𝐆 (p ⋏ q))), 𝐅 (𝐆 q)] ⊢ [𝐅 (𝐆 (p ⋏ q))] from
            .impL (A := 𝐅 (𝐆 q)) (B := 𝐅 (𝐆 (p ⋏ q))) (by simp)
              (.ax (A := 𝐅 (𝐆 q)) (by simp) (by simp))
              (.ax (A := 𝐅 (𝐆 (p ⋏ q))) (by simp) (by simp)))
          (by simp) (by simp))))

theorem fg_conj {AP : Type} (p q : Formula AP) :
    [𝐅 (𝐆 p), 𝐅 (𝐆 q)] ⊢ [𝐅 (𝐆 (p ⋏ q))] :=
  .evL (A := 𝐆 p) (I := (𝐅 (𝐆 q)) ⇒ (𝐅 (𝐆 (p ⋏ q)))) (by simp)
    (fg_base p q)
    (fg_stepI p q)
    (.impL (A := 𝐅 (𝐆 q)) (B := 𝐅 (𝐆 (p ⋏ q))) (by simp)
      (.ax (A := 𝐅 (𝐆 q)) (by simp) (by simp))
      (.ax (A := 𝐅 (𝐆 (p ⋏ q))) (by simp) (by simp)))

theorem candidate {AP : Type} (p q : Formula AP) :
    ([𝐅 (𝐆 ((p ⋏ q)))] ⊢ [(𝐅 (𝐆 (p)) ⋏ 𝐅 (𝐆 (q)))]) ∧ ([(𝐅 (𝐆 (p)) ⋏ 𝐅 (𝐆 (q)))] ⊢ [𝐅 (𝐆 ((p ⋏ q)))]) :=
  ⟨.andR (A := 𝐅 (𝐆 p)) (B := 𝐅 (𝐆 q)) (by simp)
      (.wk (fg_mono (p ⋏ q) p
        (.andL (A := p) (B := q) (by simp) (.ax (A := p) (by simp) (by simp))))
        (by simp) (by simp))
      (.wk (fg_mono (p ⋏ q) q
        (.andL (A := p) (B := q) (by simp) (.ax (A := q) (by simp) (by simp))))
        (by simp) (by simp)),
   .andL (A := 𝐅 (𝐆 p)) (B := 𝐅 (𝐆 q)) (by simp)
      (.wk (fg_conj p q) (by simp) (by simp))⟩

end Candidate

theorem verified {AP : Type} (p q : Formula AP) :
    ([𝐅 (𝐆 ((p ⋏ q)))] ⊢ [(𝐅 (𝐆 (p)) ⋏ 𝐅 (𝐆 (q)))]) ∧ ([(𝐅 (𝐆 (p)) ⋏ 𝐅 (𝐆 (q)))] ⊢ [𝐅 (𝐆 ((p ⋏ q)))]) :=
  Candidate.candidate p q

#print axioms verified
