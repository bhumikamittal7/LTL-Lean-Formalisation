import LTL

open LTL

-- LTL law 62: ¬◇ □ p ≈ □ ◇ ¬p
-- (the proposer's answer starts at line 9)

namespace Candidate
theorem notF_next {AP : Type} (q : Formula AP) :
    [∼(𝐅 q)] ⊢ [𝐗 (∼(𝐅 q))] :=
  .negL (A := 𝐅 q) (by simp)
    (.evR (A := q) (by simp)
      (.next (show ([] : List (Formula AP)) ⊢ [𝐅 q, ∼(𝐅 q)] from
          .negR (A := 𝐅 q) (by simp) (.ax (A := 𝐅 q) (by simp) (by simp)))
        (by simp) (by simp)))

theorem XnegG {AP : Type} (q : Formula AP) :
    [𝐗 (∼(𝐆 q))] ⊢ [∼(𝐆 q)] :=
  .negR (A := 𝐆 q) (by simp)
    (.alwaysL (A := q) (by simp)
      (.next (show [𝐆 q, ∼(𝐆 q)] ⊢ ([] : List (Formula AP)) from
          .negL (A := 𝐆 q) (by simp) (.ax (A := 𝐆 q) (by simp) (by simp)))
        (by simp) (by simp)))

theorem dir1 {AP : Type} (p : Formula AP) :
    [∼(𝐅 (𝐆 p))] ⊢ [𝐆 (𝐅 (∼p))] :=
  .alwaysR (A := 𝐅 (∼p)) (I := ∼(𝐅 (𝐆 p))) (by simp)
    (.ax (A := ∼(𝐅 (𝐆 p))) (by simp) (by simp))
    (notF_next (𝐆 p))
    (.negL (A := 𝐅 (𝐆 p)) (by simp)
      (.evR (A := 𝐆 p) (by simp)
        (.alwaysR (A := p) (I := ∼(𝐅 (∼p))) (by simp)
          (.negR (A := 𝐅 (∼p)) (by simp) (.ax (A := 𝐅 (∼p)) (by simp) (by simp)))
          (notF_next (∼p))
          (.negL (A := 𝐅 (∼p)) (by simp)
            (.evR (A := ∼p) (by simp)
              (.negR (A := p) (by simp) (.ax (A := p) (by simp) (by simp))))))))

theorem dir2 {AP : Type} (p : Formula AP) :
    [𝐆 (𝐅 (∼p))] ⊢ [∼(𝐅 (𝐆 p))] :=
  .negR (A := 𝐅 (𝐆 p)) (by simp)
    (.evL (A := 𝐆 p) (I := ∼(𝐆 (𝐅 (∼p)))) (by simp)
      (.negR (A := 𝐆 (𝐅 (∼p))) (by simp)
        (.alwaysL (A := 𝐅 (∼p)) (by simp)
          (.evL (A := ∼p) (I := ∼(𝐆 p)) (by simp)
            (.negR (A := 𝐆 p) (by simp)
              (.alwaysL (A := p) (by simp)
                (.negL (A := p) (by simp) (.ax (A := p) (by simp) (by simp)))))
            (XnegG p)
            (.negL (A := 𝐆 p) (by simp) (.ax (A := 𝐆 p) (by simp) (by simp))))))
      (XnegG (𝐅 (∼p)))
      (.negL (A := 𝐆 (𝐅 (∼p))) (by simp)
        (.ax (A := 𝐆 (𝐅 (∼p))) (by simp) (by simp))))

theorem candidate {AP : Type} (p : Formula AP) :
    ([∼(𝐅 (𝐆 (p)))] ⊢ [𝐆 (𝐅 (∼(p)))]) ∧ ([𝐆 (𝐅 (∼(p)))] ⊢ [∼(𝐅 (𝐆 (p)))]) :=
  ⟨dir1 p, dir2 p⟩

end Candidate

theorem verified {AP : Type} (p : Formula AP) :
    ([∼(𝐅 (𝐆 (p)))] ⊢ [𝐆 (𝐅 (∼(p)))]) ∧ ([𝐆 (𝐅 (∼(p)))] ⊢ [∼(𝐅 (𝐆 (p)))]) :=
  Candidate.candidate p

#print axioms verified
