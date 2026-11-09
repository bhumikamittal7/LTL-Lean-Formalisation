import Bench

open LTL LTL.System
open Bench.Robot
open Bench.Robot.P Bench.Robot.St

namespace Candidate

theorem candidate : S.hyps ⊢ [lift specReach] := by
  show [(at_ cA ⋎ ⊥ₗ), 𝐆 (at_ cA ⇒ ∼(ap dock)), 𝐆 (at_ cA ⇒ ∼(ap hazard)), 𝐆 (at_ cA ⇒ ∼(ap low)), 𝐆 (at_ cA ⇒ 𝐗 (at_ cB ⋎ (at_ cC ⋎ ⊥ₗ))), 𝐆 (at_ cB ⇒ ap low), 𝐆 (at_ cB ⇒ ∼(ap dock)), 𝐆 (at_ cB ⇒ ∼(ap hazard)), 𝐆 (at_ cB ⇒ 𝐗 (at_ cC ⋎ ⊥ₗ)), 𝐆 (at_ cC ⇒ ∼(ap dock)), 𝐆 (at_ cC ⇒ ∼(ap hazard)), 𝐆 (at_ cC ⇒ ∼(ap low)), 𝐆 (at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)), 𝐆 (at_ cDock ⇒ ap dock), 𝐆 (at_ cDock ⇒ ∼(ap hazard)), 𝐆 (at_ cDock ⇒ ∼(ap low)), 𝐆 (at_ cDock ⇒ 𝐗 (at_ cA ⋎ ⊥ₗ)), 𝐆 (at_ cHaz ⇒ ap hazard), 𝐆 (at_ cHaz ⇒ ∼(ap dock)), 𝐆 (at_ cHaz ⇒ ∼(ap low)), 𝐆 (at_ cHaz ⇒ 𝐗 (at_ cHaz ⋎ ⊥ₗ))] ⊢ [(∼(ap hazard) 𝐔 ap dock)]
  exact .orL (A := at_ cA) (B := ⊥ₗ) (by simp)
    (.untilR (A := ∼(ap hazard)) (B := ap dock) (by simp)
      (.negR (A := ap hazard) (by simp)
        (.alwaysL (A := at_ cA ⇒ ∼(ap hazard)) (by simp)
          (.impL (A := at_ cA) (B := ∼(ap hazard)) (by simp) (.close (by decide)) (.close (by decide)))))
      (.alwaysL (A := at_ cA ⇒ 𝐗 (at_ cB ⋎ (at_ cC ⋎ ⊥ₗ))) (by simp)
       (.alwaysL (A := at_ cB ⇒ ∼(ap hazard)) (by simp)
        (.alwaysL (A := at_ cB ⇒ 𝐗 (at_ cC ⋎ ⊥ₗ)) (by simp)
         (.alwaysL (A := at_ cC ⇒ ∼(ap hazard)) (by simp)
          (.alwaysL (A := at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)) (by simp)
           (.alwaysL (A := at_ cDock ⇒ ap dock) (by simp)
            (.impL (A := at_ cA) (B := 𝐗 (at_ cB ⋎ (at_ cC ⋎ ⊥ₗ))) (by simp) (.close (by decide))
              (.step (Γ' := [at_ cB ⋎ (at_ cC ⋎ ⊥ₗ), 𝐆 (at_ cB ⇒ ∼(ap hazard)), 𝐆 (at_ cB ⇒ 𝐗 (at_ cC ⋎ ⊥ₗ)), 𝐆 (at_ cC ⇒ ∼(ap hazard)), 𝐆 (at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)), 𝐆 (at_ cDock ⇒ ap dock)]) (B := (∼(ap hazard) 𝐔 ap dock))
                (.orL (A := at_ cB) (B := at_ cC ⋎ ⊥ₗ) (by simp)
                  -- state cB
                  (.untilR (A := ∼(ap hazard)) (B := ap dock) (by simp)
                    (.negR (A := ap hazard) (by simp)
                      (.alwaysL (A := at_ cB ⇒ ∼(ap hazard)) (by simp)
                        (.impL (A := at_ cB) (B := ∼(ap hazard)) (by simp) (.close (by decide)) (.close (by decide)))))
                    (.alwaysL (A := at_ cB ⇒ 𝐗 (at_ cC ⋎ ⊥ₗ)) (by simp)
                     (.alwaysL (A := at_ cC ⇒ ∼(ap hazard)) (by simp)
                      (.alwaysL (A := at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)) (by simp)
                       (.alwaysL (A := at_ cDock ⇒ ap dock) (by simp)
                        (.impL (A := at_ cB) (B := 𝐗 (at_ cC ⋎ ⊥ₗ)) (by simp) (.close (by decide))
                          (.step (Γ' := [at_ cC ⋎ ⊥ₗ, 𝐆 (at_ cC ⇒ ∼(ap hazard)), 𝐆 (at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)), 𝐆 (at_ cDock ⇒ ap dock)]) (B := (∼(ap hazard) 𝐔 ap dock))
                            -- state cC
                            (.orL (A := at_ cC) (B := ⊥ₗ) (by simp)
                              (.untilR (A := ∼(ap hazard)) (B := ap dock) (by simp)
                                (.negR (A := ap hazard) (by simp)
                                  (.alwaysL (A := at_ cC ⇒ ∼(ap hazard)) (by simp)
                                    (.impL (A := at_ cC) (B := ∼(ap hazard)) (by simp) (.close (by decide)) (.close (by decide)))))
                                (.alwaysL (A := at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)) (by simp)
                                  (.alwaysL (A := at_ cDock ⇒ ap dock) (by simp)
                                    (.impL (A := at_ cC) (B := 𝐗 (at_ cDock ⋎ ⊥ₗ)) (by simp) (.close (by decide))
                                      (.step (Γ' := [at_ cDock ⋎ ⊥ₗ, 𝐆 (at_ cDock ⇒ ap dock)]) (B := (∼(ap hazard) 𝐔 ap dock))
                                        (.orL (A := at_ cDock) (B := ⊥ₗ) (by simp)
                                          (.alwaysL (A := at_ cDock ⇒ ap dock) (by simp)
                                            (.impL (A := at_ cDock) (B := ap dock) (by simp) (.close (by decide))
                                              (.untilR (A := ∼(ap hazard)) (B := ap dock) (by simp) (.close (by decide)) (.close (by decide)))))
                                          (.botL (by simp)))
                                        (by simp) (by simp))))))
                              (.botL (by simp)))
                            (by simp) (by simp))))))))
                  -- state cC (direct from cA)
                  (.orL (A := at_ cC) (B := ⊥ₗ) (by simp)
                    (.untilR (A := ∼(ap hazard)) (B := ap dock) (by simp)
                      (.negR (A := ap hazard) (by simp)
                        (.alwaysL (A := at_ cC ⇒ ∼(ap hazard)) (by simp)
                          (.impL (A := at_ cC) (B := ∼(ap hazard)) (by simp) (.close (by decide)) (.close (by decide)))))
                      (.alwaysL (A := at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)) (by simp)
                        (.alwaysL (A := at_ cDock ⇒ ap dock) (by simp)
                          (.impL (A := at_ cC) (B := 𝐗 (at_ cDock ⋎ ⊥ₗ)) (by simp) (.close (by decide))
                            (.step (Γ' := [at_ cDock ⋎ ⊥ₗ, 𝐆 (at_ cDock ⇒ ap dock)]) (B := (∼(ap hazard) 𝐔 ap dock))
                              (.orL (A := at_ cDock) (B := ⊥ₗ) (by simp)
                                (.alwaysL (A := at_ cDock ⇒ ap dock) (by simp)
                                  (.impL (A := at_ cDock) (B := ap dock) (by simp) (.close (by decide))
                                    (.untilR (A := ∼(ap hazard)) (B := ap dock) (by simp) (.close (by decide)) (.close (by decide)))))
                                (.botL (by simp)))
                              (by simp) (by simp))))))
                    (.botL (by simp))))
                (by simp) (by simp))))))))))
    (.botL (by simp))

end Candidate

theorem verified : Bench.Robot.S.Models Bench.Robot.specReach :=
  Bench.Robot.S.sat_of_derives Candidate.candidate

#print axioms verified
