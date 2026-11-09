import Bench

open LTL LTL.System
open Bench.Robot
open Bench.Robot.P Bench.Robot.St

namespace Candidate

abbrev qR4 : Formula (P ⊕ St) := at_ cDock ⋎ ⊥ₗ
abbrev qR3 : Formula (P ⊕ St) := at_ cC ⋎ qR4
abbrev qR2 : Formula (P ⊕ St) := at_ cB ⋎ qR3
abbrev qR : Formula (P ⊕ St) := at_ cA ⋎ qR2
abbrev qDA : Formula (P ⊕ St) := at_ cB ⋎ (at_ cC ⋎ ⊥ₗ)
abbrev a2 : Formula (P ⊕ St) := at_ cA ⇒ ∼(ap hazard)
abbrev a4 : Formula (P ⊕ St) := at_ cA ⇒ 𝐗 (at_ cB ⋎ (at_ cC ⋎ ⊥ₗ))
abbrev a7 : Formula (P ⊕ St) := at_ cB ⇒ ∼(ap hazard)
abbrev a8 : Formula (P ⊕ St) := at_ cB ⇒ 𝐗 (at_ cC ⋎ ⊥ₗ)
abbrev a10 : Formula (P ⊕ St) := at_ cC ⇒ ∼(ap hazard)
abbrev a12 : Formula (P ⊕ St) := at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)
abbrev a14 : Formula (P ⊕ St) := at_ cDock ⇒ ∼(ap hazard)
abbrev a16 : Formula (P ⊕ St) := at_ cDock ⇒ 𝐗 (at_ cA ⋎ ⊥ₗ)
abbrev qC7 : Formula (P ⊕ St) := (𝐆 a14) ⋏ (𝐆 a16)
abbrev qC6 : Formula (P ⊕ St) := (𝐆 a12) ⋏ qC7
abbrev qC5 : Formula (P ⊕ St) := (𝐆 a10) ⋏ qC6
abbrev qC4 : Formula (P ⊕ St) := (𝐆 a8) ⋏ qC5
abbrev qC3 : Formula (P ⊕ St) := (𝐆 a7) ⋏ qC4
abbrev qC2 : Formula (P ⊕ St) := (𝐆 a4) ⋏ qC3
abbrev qC : Formula (P ⊕ St) := (𝐆 a2) ⋏ qC2
abbrev Inv : Formula (P ⊕ St) := qR ⋏ qC

theorem candidate : S.hyps ⊢ [lift specSafe] := by
  show [(at_ cA ⋎ ⊥ₗ), 𝐆 (at_ cA ⇒ ∼(ap dock)), 𝐆 (at_ cA ⇒ ∼(ap hazard)), 𝐆 (at_ cA ⇒ ∼(ap low)), 𝐆 (at_ cA ⇒ 𝐗 (at_ cB ⋎ (at_ cC ⋎ ⊥ₗ))), 𝐆 (at_ cB ⇒ ap low), 𝐆 (at_ cB ⇒ ∼(ap dock)), 𝐆 (at_ cB ⇒ ∼(ap hazard)), 𝐆 (at_ cB ⇒ 𝐗 (at_ cC ⋎ ⊥ₗ)), 𝐆 (at_ cC ⇒ ∼(ap dock)), 𝐆 (at_ cC ⇒ ∼(ap hazard)), 𝐆 (at_ cC ⇒ ∼(ap low)), 𝐆 (at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)), 𝐆 (at_ cDock ⇒ ap dock), 𝐆 (at_ cDock ⇒ ∼(ap hazard)), 𝐆 (at_ cDock ⇒ ∼(ap low)), 𝐆 (at_ cDock ⇒ 𝐗 (at_ cA ⋎ ⊥ₗ)), 𝐆 (at_ cHaz ⇒ ap hazard), 𝐆 (at_ cHaz ⇒ ∼(ap dock)), 𝐆 (at_ cHaz ⇒ ∼(ap low)), 𝐆 (at_ cHaz ⇒ 𝐗 (at_ cHaz ⋎ ⊥ₗ))] ⊢ [𝐆 (∼(ap hazard))]
  exact
    .alwaysR (A := ∼(ap hazard)) (I := Inv) (by simp)
      (.andR (A := qR) (B := qC) (by simp)
        (.orL (A := at_ cA) (B := ⊥ₗ) (by simp)
          (.orR (A := at_ cA) (B := qR2) (by simp) (.close (by decide)))
          (.botL (by simp)))
        (.andR (A := 𝐆 a2) (B := qC2) (by simp) (.close (by decide))
         (.andR (A := 𝐆 a4) (B := qC3) (by simp) (.close (by decide))
         (.andR (A := 𝐆 a7) (B := qC4) (by simp) (.close (by decide))
         (.andR (A := 𝐆 a8) (B := qC5) (by simp) (.close (by decide))
         (.andR (A := 𝐆 a10) (B := qC6) (by simp) (.close (by decide))
         (.andR (A := 𝐆 a12) (B := qC7) (by simp) (.close (by decide))
         (.andR (A := 𝐆 a14) (B := 𝐆 a16) (by simp) (.close (by decide)) (.close (by decide))))))))))
      (.andL (A := qR) (B := qC) (by simp) <|
       .andL (A := 𝐆 a2) (B := qC2) (by simp) <|
       .andL (A := 𝐆 a4) (B := qC3) (by simp) <|
       .andL (A := 𝐆 a7) (B := qC4) (by simp) <|
       .andL (A := 𝐆 a8) (B := qC5) (by simp) <|
       .andL (A := 𝐆 a10) (B := qC6) (by simp) <|
       .andL (A := 𝐆 a12) (B := qC7) (by simp) <|
       .andL (A := 𝐆 a14) (B := 𝐆 a16) (by simp) <|
       .alwaysL (A := a2) (by simp) <|
       .alwaysL (A := a4) (by simp) <|
       .alwaysL (A := a7) (by simp) <|
       .alwaysL (A := a8) (by simp) <|
       .alwaysL (A := a10) (by simp) <|
       .alwaysL (A := a12) (by simp) <|
       .alwaysL (A := a14) (by simp) <|
       .alwaysL (A := a16) (by simp) <|
       .cut (A := 𝐗 qR)
        (.orL (A := at_ cA) (B := qR2) (by simp)
          (.impL (A := at_ cA) (B := 𝐗 qDA) (by simp) (.close (by decide))
            (.step (Γ' := [qDA]) (B := qR)
              (.orR (A := at_ cA) (B := qR2) (by simp) <| .orR (A := at_ cB) (B := qR3) (by simp) <|
               .orR (A := at_ cC) (B := qR4) (by simp) <| .orR (A := at_ cDock) (B := ⊥ₗ) (by simp) <|
               .orL (A := at_ cB) (B := at_ cC ⋎ ⊥ₗ) (by simp) (.close (by decide))
                (.orL (A := at_ cC) (B := ⊥ₗ) (by simp) (.close (by decide)) (.botL (by simp))))
              (by simp) (by simp)))
          (.orL (A := at_ cB) (B := qR3) (by simp)
            (.impL (A := at_ cB) (B := 𝐗 (at_ cC ⋎ ⊥ₗ)) (by simp) (.close (by decide))
              (.step (Γ' := [at_ cC ⋎ ⊥ₗ]) (B := qR)
                (.orR (A := at_ cA) (B := qR2) (by simp) <| .orR (A := at_ cB) (B := qR3) (by simp) <|
                 .orR (A := at_ cC) (B := qR4) (by simp) <| .orR (A := at_ cDock) (B := ⊥ₗ) (by simp) <|
                 .orL (A := at_ cC) (B := ⊥ₗ) (by simp) (.close (by decide)) (.botL (by simp)))
                (by simp) (by simp)))
            (.orL (A := at_ cC) (B := qR4) (by simp)
              (.impL (A := at_ cC) (B := 𝐗 qR4) (by simp) (.close (by decide))
                (.step (Γ' := [qR4]) (B := qR)
                  (.orR (A := at_ cA) (B := qR2) (by simp) <| .orR (A := at_ cB) (B := qR3) (by simp) <|
                   .orR (A := at_ cC) (B := qR4) (by simp) <| .orR (A := at_ cDock) (B := ⊥ₗ) (by simp) <|
                   .close (by decide))
                  (by simp) (by simp)))
              (.orL (A := at_ cDock) (B := ⊥ₗ) (by simp)
                (.impL (A := at_ cDock) (B := 𝐗 (at_ cA ⋎ ⊥ₗ)) (by simp) (.close (by decide))
                  (.step (Γ' := [at_ cA ⋎ ⊥ₗ]) (B := qR)
                    (.orR (A := at_ cA) (B := qR2) (by simp) <| .orR (A := at_ cB) (B := qR3) (by simp) <|
                     .orR (A := at_ cC) (B := qR4) (by simp) <| .orR (A := at_ cDock) (B := ⊥ₗ) (by simp) <|
                     .orL (A := at_ cA) (B := ⊥ₗ) (by simp) (.close (by decide)) (.botL (by simp)))
                    (by simp) (by simp)))
                (.botL (by simp))))))
        (.step (Γ' := [qR, 𝐆 a2, 𝐆 a4, 𝐆 a7, 𝐆 a8, 𝐆 a10, 𝐆 a12, 𝐆 a14, 𝐆 a16]) (B := Inv)
          (.andR (A := qR) (B := qC) (by simp) (.close (by decide))
            (.andR (A := 𝐆 a2) (B := qC2) (by simp) (.close (by decide))
             (.andR (A := 𝐆 a4) (B := qC3) (by simp) (.close (by decide))
             (.andR (A := 𝐆 a7) (B := qC4) (by simp) (.close (by decide))
             (.andR (A := 𝐆 a8) (B := qC5) (by simp) (.close (by decide))
             (.andR (A := 𝐆 a10) (B := qC6) (by simp) (.close (by decide))
             (.andR (A := 𝐆 a12) (B := qC7) (by simp) (.close (by decide))
             (.andR (A := 𝐆 a14) (B := 𝐆 a16) (by simp) (.close (by decide)) (.close (by decide))))))))))
          (by simp) (by simp)))
      (.andL (A := qR) (B := qC) (by simp) <|
       .andL (A := 𝐆 a2) (B := qC2) (by simp) <|
       .andL (A := 𝐆 a4) (B := qC3) (by simp) <|
       .andL (A := 𝐆 a7) (B := qC4) (by simp) <|
       .andL (A := 𝐆 a8) (B := qC5) (by simp) <|
       .andL (A := 𝐆 a10) (B := qC6) (by simp) <|
       .andL (A := 𝐆 a12) (B := qC7) (by simp) <|
       .andL (A := 𝐆 a14) (B := 𝐆 a16) (by simp) <|
       .alwaysL (A := a2) (by simp) <|
       .alwaysL (A := a7) (by simp) <|
       .alwaysL (A := a10) (by simp) <|
       .alwaysL (A := a14) (by simp) <|
       .orL (A := at_ cA) (B := qR2) (by simp)
        (.impL (A := at_ cA) (B := ∼(ap hazard)) (by simp) (.close (by decide)) (.close (by decide)))
        (.orL (A := at_ cB) (B := qR3) (by simp)
          (.impL (A := at_ cB) (B := ∼(ap hazard)) (by simp) (.close (by decide)) (.close (by decide)))
          (.orL (A := at_ cC) (B := qR4) (by simp)
            (.impL (A := at_ cC) (B := ∼(ap hazard)) (by simp) (.close (by decide)) (.close (by decide)))
            (.orL (A := at_ cDock) (B := ⊥ₗ) (by simp)
              (.impL (A := at_ cDock) (B := ∼(ap hazard)) (by simp) (.close (by decide)) (.close (by decide)))
              (.botL (by simp))))))

end Candidate

theorem verified : Bench.Robot.S.Models Bench.Robot.specSafe :=
  Bench.Robot.S.sat_of_derives Candidate.candidate

#print axioms verified
