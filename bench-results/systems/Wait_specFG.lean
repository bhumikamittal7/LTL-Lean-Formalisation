import Bench

open LTL LTL.System
open Bench.Wait
open Bench.Wait.P Bench.Wait.St

namespace Candidate

abbrev inv : Formula (P ⊕ St) :=
  (at_ q1 ⋎ ⊥ₗ) ⋏ ((𝐆 (at_ q1 ⇒ ap done)) ⋏ (𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ))))

theorem candidate : S.hyps ⊢ [lift specFG] := by
  show [(at_ q0 ⋎ ⊥ₗ), 𝐆 (at_ q0 ⇒ ap wait), 𝐆 (at_ q0 ⇒ ∼(ap done)), 𝐆 (at_ q0 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ)), 𝐆 (at_ q1 ⇒ ap done), 𝐆 (at_ q1 ⇒ ∼(ap wait)), 𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ))] ⊢ [𝐅 (𝐆 (ap done))]
  exact
    .orL (A := at_ q0) (B := ⊥ₗ) (by simp)
      (.alwaysL (A := at_ q0 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ)) (by simp)
        (.alwaysL (A := at_ q1 ⇒ ap done) (by simp)
          (.alwaysL (A := at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ)) (by simp)
            (.impL (A := at_ q0) (B := 𝐗 (at_ q1 ⋎ ⊥ₗ)) (by simp)
              (.close (by decide))
              (.evR (A := 𝐆 (ap done)) (by simp)
                (.step (Γ' := [(at_ q1 ⋎ ⊥ₗ), 𝐆 (at_ q1 ⇒ ap done), 𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ))])
                  (B := 𝐅 (𝐆 (ap done)))
                  (.evR (A := 𝐆 (ap done)) (by simp)
                    (.alwaysR (I := inv) (A := ap done) (by simp)
                      -- I holds now
                      (.andR (A := (at_ q1 ⋎ ⊥ₗ))
                          (B := (𝐆 (at_ q1 ⇒ ap done)) ⋏ (𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ)))) (by simp [inv])
                        (.close (by decide))
                        (.andR (A := 𝐆 (at_ q1 ⇒ ap done)) (B := 𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ))) (by simp)
                          (.close (by decide))
                          (.close (by decide))))
                      -- I preserved
                      (.andL (A := (at_ q1 ⋎ ⊥ₗ))
                          (B := (𝐆 (at_ q1 ⇒ ap done)) ⋏ (𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ)))) (by simp [inv])
                        (.andL (A := 𝐆 (at_ q1 ⇒ ap done)) (B := 𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ))) (by simp)
                          (.orL (A := at_ q1) (B := ⊥ₗ) (by simp)
                            (.alwaysL (A := at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ)) (by simp)
                              (.alwaysL (A := at_ q1 ⇒ ap done) (by simp)
                                (.impL (A := at_ q1) (B := 𝐗 (at_ q1 ⋎ ⊥ₗ)) (by simp)
                                  (.close (by decide))
                                  (.step (Γ' := [(at_ q1 ⋎ ⊥ₗ), 𝐆 (at_ q1 ⇒ ap done), 𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ))])
                                    (B := inv)
                                    (.andR (A := (at_ q1 ⋎ ⊥ₗ))
                                        (B := (𝐆 (at_ q1 ⇒ ap done)) ⋏ (𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ)))) (by simp [inv])
                                      (.close (by decide))
                                      (.andR (A := 𝐆 (at_ q1 ⇒ ap done)) (B := 𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ))) (by simp)
                                        (.close (by decide))
                                        (.close (by decide))))
                                    (by simp) (by simp [inv])))))
                            (.botL (by simp)))))
                      -- I implies done
                      (.andL (A := (at_ q1 ⋎ ⊥ₗ))
                          (B := (𝐆 (at_ q1 ⇒ ap done)) ⋏ (𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ)))) (by simp [inv])
                        (.andL (A := 𝐆 (at_ q1 ⇒ ap done)) (B := 𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ))) (by simp)
                          (.orL (A := at_ q1) (B := ⊥ₗ) (by simp)
                            (.alwaysL (A := at_ q1 ⇒ ap done) (by simp)
                              (.impL (A := at_ q1) (B := ap done) (by simp)
                                (.close (by decide))
                                (.close (by decide))))
                            (.botL (by simp)))))))
                  (by simp) (by simp)))))))
      (.botL (by simp))

end Candidate

theorem verified : Bench.Wait.S.Models Bench.Wait.specFG :=
  Bench.Wait.S.sat_of_derives Candidate.candidate

#print axioms verified
