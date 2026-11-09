import Bench

open LTL LTL.System
open Bench.Wait
open Bench.Wait.P Bench.Wait.St

namespace Candidate

abbrev Ugoal : Formula (P ⊕ St) := (ap wait 𝐔 ap done)

abbrev Inner : [(at_ q1 ⋎ ⊥ₗ), 𝐆 (at_ q1 ⇒ ap done)] ⊢ [Ugoal] :=
  .orL (A := at_ q1) (B := ⊥ₗ) (by simp)
    (.alwaysL (A := at_ q1 ⇒ ap done) (by simp)
      (.impL (A := at_ q1) (B := ap done) (by simp)
        (.close (by decide))
        (.untilR (A := ap wait) (B := ap done) (by simp)
          (.close (by decide))
          (.close (by decide)))))
    (.botL (by simp))

theorem candidate : S.hyps ⊢ [lift specUntil] := by
  show [(at_ q0 ⋎ ⊥ₗ), 𝐆 (at_ q0 ⇒ ap wait), 𝐆 (at_ q0 ⇒ ∼(ap done)), 𝐆 (at_ q0 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ)), 𝐆 (at_ q1 ⇒ ap done), 𝐆 (at_ q1 ⇒ ∼(ap wait)), 𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ))] ⊢ [(ap wait 𝐔 ap done)]
  exact
    .orL (A := at_ q0) (B := ⊥ₗ) (by simp)
      (.alwaysL (A := at_ q0 ⇒ ap wait) (by simp)
        (.impL (A := at_ q0) (B := ap wait) (by simp)
          (.close (by decide))
          (.alwaysL (A := at_ q0 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ)) (by simp)
            (.impL (A := at_ q0) (B := 𝐗 (at_ q1 ⋎ ⊥ₗ)) (by simp)
              (.close (by decide))
              (.alwaysL (A := at_ q1 ⇒ ap done) (by simp)
                (.untilR (A := ap wait) (B := ap done) (by simp)
                  (.close (by decide))
                  (Derives.step (Γ' := [(at_ q1 ⋎ ⊥ₗ), 𝐆 (at_ q1 ⇒ ap done)]) (B := Ugoal)
                    Inner (by simp) (by simp))))))))
      (.botL (by simp))

end Candidate

theorem verified : Bench.Wait.S.Models Bench.Wait.specUntil :=
  Bench.Wait.S.sat_of_derives Candidate.candidate

#print axioms verified
