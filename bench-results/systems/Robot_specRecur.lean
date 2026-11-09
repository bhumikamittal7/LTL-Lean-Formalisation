import Bench

open LTL LTL.System
open Bench.Robot
open Bench.Robot.P Bench.Robot.St

namespace Candidate

abbrev FD : Formula (P ⊕ St) := 𝐅 (ap dock)
abbrev gA : Formula (P ⊕ St) := 𝐆 (at_ cA ⇒ 𝐗 (at_ cB ⋎ (at_ cC ⋎ ⊥ₗ)))
abbrev gB : Formula (P ⊕ St) := 𝐆 (at_ cB ⇒ 𝐗 (at_ cC ⋎ ⊥ₗ))
abbrev gC : Formula (P ⊕ St) := 𝐆 (at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ))
abbrev gD : Formula (P ⊕ St) := 𝐆 (at_ cDock ⇒ 𝐗 (at_ cA ⋎ ⊥ₗ))
abbrev gK : Formula (P ⊕ St) := 𝐆 (at_ cDock ⇒ ap dock)
abbrev PosI : Formula (P ⊕ St) := at_ cA ⋎ (at_ cB ⋎ (at_ cC ⋎ at_ cDock))
abbrev Gs : Formula (P ⊕ St) := gA ⋏ (gB ⋏ (gC ⋏ (gD ⋏ gK)))
abbrev InvR : Formula (P ⊕ St) := PosI ⋏ Gs

theorem lD : [at_ cDock, gK] ⊢ [FD] :=
  .evR (A := ap dock) (by simp)
    (.alwaysL (A := at_ cDock ⇒ ap dock) (by simp)
      (.impL (A := at_ cDock) (B := ap dock) (by simp)
        (.close (by decide)) (.close (by decide))))

theorem lD' : [at_ cDock ⋎ ⊥ₗ, gK] ⊢ [FD] :=
  .orL (A := at_ cDock) (B := ⊥ₗ) (by simp) (.wk lD (by simp) (by simp)) (.botL (by simp))

theorem lC : [at_ cC, gC, gK] ⊢ [FD] :=
  .evR (A := ap dock) (by simp)
    (.alwaysL (A := at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)) (by simp)
      (.alwaysL (A := at_ cDock ⇒ ap dock) (by simp)
        (.impL (A := at_ cC) (B := 𝐗 (at_ cDock ⋎ ⊥ₗ)) (by simp)
          (.close (by decide))
          (.step (Γ' := [at_ cDock ⋎ ⊥ₗ, gK]) lD' (by simp) (by simp)))))

theorem lC' : [at_ cC ⋎ ⊥ₗ, gC, gK] ⊢ [FD] :=
  .orL (A := at_ cC) (B := ⊥ₗ) (by simp) (.wk lC (by simp) (by simp)) (.botL (by simp))

theorem lB : [at_ cB, gB, gC, gK] ⊢ [FD] :=
  .evR (A := ap dock) (by simp)
    (.alwaysL (A := at_ cB ⇒ 𝐗 (at_ cC ⋎ ⊥ₗ)) (by simp)
      (.alwaysL (A := at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)) (by simp)
        (.alwaysL (A := at_ cDock ⇒ ap dock) (by simp)
          (.impL (A := at_ cB) (B := 𝐗 (at_ cC ⋎ ⊥ₗ)) (by simp)
            (.close (by decide))
            (.step (Γ' := [at_ cC ⋎ ⊥ₗ, gC, gK]) lC' (by simp) (by simp))))))

theorem lB' : [at_ cB ⋎ (at_ cC ⋎ ⊥ₗ), gB, gC, gK] ⊢ [FD] :=
  .orL (A := at_ cB) (B := at_ cC ⋎ ⊥ₗ) (by simp) (.wk lB (by simp) (by simp))
    (.orL (A := at_ cC) (B := ⊥ₗ) (by simp) (.wk lC (by simp) (by simp)) (.botL (by simp)))

theorem lA : [at_ cA, gA, gB, gC, gK] ⊢ [FD] :=
  .evR (A := ap dock) (by simp)
    (.alwaysL (A := at_ cA ⇒ 𝐗 (at_ cB ⋎ (at_ cC ⋎ ⊥ₗ))) (by simp)
      (.alwaysL (A := at_ cB ⇒ 𝐗 (at_ cC ⋎ ⊥ₗ)) (by simp)
        (.alwaysL (A := at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)) (by simp)
          (.alwaysL (A := at_ cDock ⇒ ap dock) (by simp)
            (.impL (A := at_ cA) (B := 𝐗 (at_ cB ⋎ (at_ cC ⋎ ⊥ₗ))) (by simp)
              (.close (by decide))
              (.step (Γ' := [at_ cB ⋎ (at_ cC ⋎ ⊥ₗ), gB, gC, gK]) lB' (by simp) (by simp)))))))

theorem lGoal : [InvR] ⊢ [FD] :=
  .andL (A := PosI) (B := Gs) (by simp)
  (.andL (A := gA) (B := gB ⋏ (gC ⋏ (gD ⋏ gK))) (by simp)
  (.andL (A := gB) (B := gC ⋏ (gD ⋏ gK)) (by simp)
  (.andL (A := gC) (B := gD ⋏ gK) (by simp)
  (.andL (A := gD) (B := gK) (by simp)
  (.orL (A := at_ cA) (B := at_ cB ⋎ (at_ cC ⋎ at_ cDock)) (by simp)
    (.wk lA (by simp) (by simp))
  (.orL (A := at_ cB) (B := at_ cC ⋎ at_ cDock) (by simp)
    (.wk lB (by simp) (by simp))
  (.orL (A := at_ cC) (B := at_ cDock) (by simp)
    (.wk lC (by simp) (by simp))
    (.wk lD (by simp) (by simp)))))))))

theorem lGs : [gA, gB, gC, gD, gK] ⊢ [Gs] :=
  .andR (A := gA) (B := gB ⋏ (gC ⋏ (gD ⋏ gK))) (by simp) (.close (by decide))
  (.andR (A := gB) (B := gC ⋏ (gD ⋏ gK)) (by simp) (.close (by decide))
  (.andR (A := gC) (B := gD ⋏ gK) (by simp) (.close (by decide))
  (.andR (A := gD) (B := gK) (by simp) (.close (by decide)) (.close (by decide)))))

theorem bA : [at_ cA, gA, gB, gC, gD, gK] ⊢ [InvR] :=
  .andR (A := PosI) (B := Gs) (by simp)
    (.orR (A := at_ cA) (B := at_ cB ⋎ (at_ cC ⋎ at_ cDock)) (by simp) (.close (by decide)))
    (.wk lGs (by simp) (by simp))

theorem bB : [at_ cB, gA, gB, gC, gD, gK] ⊢ [InvR] :=
  .andR (A := PosI) (B := Gs) (by simp)
    (.orR (A := at_ cA) (B := at_ cB ⋎ (at_ cC ⋎ at_ cDock)) (by simp)
      (.orR (A := at_ cB) (B := at_ cC ⋎ at_ cDock) (by simp) (.close (by decide))))
    (.wk lGs (by simp) (by simp))

theorem bC : [at_ cC, gA, gB, gC, gD, gK] ⊢ [InvR] :=
  .andR (A := PosI) (B := Gs) (by simp)
    (.orR (A := at_ cA) (B := at_ cB ⋎ (at_ cC ⋎ at_ cDock)) (by simp)
      (.orR (A := at_ cB) (B := at_ cC ⋎ at_ cDock) (by simp)
        (.orR (A := at_ cC) (B := at_ cDock) (by simp) (.close (by decide)))))
    (.wk lGs (by simp) (by simp))

theorem bD : [at_ cDock, gA, gB, gC, gD, gK] ⊢ [InvR] :=
  .andR (A := PosI) (B := Gs) (by simp)
    (.orR (A := at_ cA) (B := at_ cB ⋎ (at_ cC ⋎ at_ cDock)) (by simp)
      (.orR (A := at_ cB) (B := at_ cC ⋎ at_ cDock) (by simp)
        (.orR (A := at_ cC) (B := at_ cDock) (by simp) (.close (by decide)))))
    (.wk lGs (by simp) (by simp))

theorem nA : [at_ cB ⋎ (at_ cC ⋎ ⊥ₗ), gA, gB, gC, gD, gK] ⊢ [InvR] :=
  .orL (A := at_ cB) (B := at_ cC ⋎ ⊥ₗ) (by simp) (.wk bB (by simp) (by simp))
    (.orL (A := at_ cC) (B := ⊥ₗ) (by simp) (.wk bC (by simp) (by simp)) (.botL (by simp)))

theorem nB : [at_ cC ⋎ ⊥ₗ, gA, gB, gC, gD, gK] ⊢ [InvR] :=
  .orL (A := at_ cC) (B := ⊥ₗ) (by simp) (.wk bC (by simp) (by simp)) (.botL (by simp))

theorem nC : [at_ cDock ⋎ ⊥ₗ, gA, gB, gC, gD, gK] ⊢ [InvR] :=
  .orL (A := at_ cDock) (B := ⊥ₗ) (by simp) (.wk bD (by simp) (by simp)) (.botL (by simp))

theorem nD : [at_ cA ⋎ ⊥ₗ, gA, gB, gC, gD, gK] ⊢ [InvR] :=
  .orL (A := at_ cA) (B := ⊥ₗ) (by simp) (.wk bA (by simp) (by simp)) (.botL (by simp))

theorem sA : [at_ cA, gA, gB, gC, gD, gK] ⊢ [𝐗 InvR] :=
  .alwaysL (A := at_ cA ⇒ 𝐗 (at_ cB ⋎ (at_ cC ⋎ ⊥ₗ))) (by simp)
  (.alwaysL (A := at_ cB ⇒ 𝐗 (at_ cC ⋎ ⊥ₗ)) (by simp)
  (.alwaysL (A := at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)) (by simp)
  (.alwaysL (A := at_ cDock ⇒ 𝐗 (at_ cA ⋎ ⊥ₗ)) (by simp)
  (.alwaysL (A := at_ cDock ⇒ ap dock) (by simp)
  (.impL (A := at_ cA) (B := 𝐗 (at_ cB ⋎ (at_ cC ⋎ ⊥ₗ))) (by simp) (.close (by decide))
    (.step (Γ' := [at_ cB ⋎ (at_ cC ⋎ ⊥ₗ), gA, gB, gC, gD, gK]) nA (by simp) (by simp)))))))

theorem sB : [at_ cB, gA, gB, gC, gD, gK] ⊢ [𝐗 InvR] :=
  .alwaysL (A := at_ cA ⇒ 𝐗 (at_ cB ⋎ (at_ cC ⋎ ⊥ₗ))) (by simp)
  (.alwaysL (A := at_ cB ⇒ 𝐗 (at_ cC ⋎ ⊥ₗ)) (by simp)
  (.alwaysL (A := at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)) (by simp)
  (.alwaysL (A := at_ cDock ⇒ 𝐗 (at_ cA ⋎ ⊥ₗ)) (by simp)
  (.alwaysL (A := at_ cDock ⇒ ap dock) (by simp)
  (.impL (A := at_ cB) (B := 𝐗 (at_ cC ⋎ ⊥ₗ)) (by simp) (.close (by decide))
    (.step (Γ' := [at_ cC ⋎ ⊥ₗ, gA, gB, gC, gD, gK]) nB (by simp) (by simp)))))))

theorem sC : [at_ cC, gA, gB, gC, gD, gK] ⊢ [𝐗 InvR] :=
  .alwaysL (A := at_ cA ⇒ 𝐗 (at_ cB ⋎ (at_ cC ⋎ ⊥ₗ))) (by simp)
  (.alwaysL (A := at_ cB ⇒ 𝐗 (at_ cC ⋎ ⊥ₗ)) (by simp)
  (.alwaysL (A := at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)) (by simp)
  (.alwaysL (A := at_ cDock ⇒ 𝐗 (at_ cA ⋎ ⊥ₗ)) (by simp)
  (.alwaysL (A := at_ cDock ⇒ ap dock) (by simp)
  (.impL (A := at_ cC) (B := 𝐗 (at_ cDock ⋎ ⊥ₗ)) (by simp) (.close (by decide))
    (.step (Γ' := [at_ cDock ⋎ ⊥ₗ, gA, gB, gC, gD, gK]) nC (by simp) (by simp)))))))

theorem sD : [at_ cDock, gA, gB, gC, gD, gK] ⊢ [𝐗 InvR] :=
  .alwaysL (A := at_ cA ⇒ 𝐗 (at_ cB ⋎ (at_ cC ⋎ ⊥ₗ))) (by simp)
  (.alwaysL (A := at_ cB ⇒ 𝐗 (at_ cC ⋎ ⊥ₗ)) (by simp)
  (.alwaysL (A := at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)) (by simp)
  (.alwaysL (A := at_ cDock ⇒ 𝐗 (at_ cA ⋎ ⊥ₗ)) (by simp)
  (.alwaysL (A := at_ cDock ⇒ ap dock) (by simp)
  (.impL (A := at_ cDock) (B := 𝐗 (at_ cA ⋎ ⊥ₗ)) (by simp) (.close (by decide))
    (.step (Γ' := [at_ cA ⋎ ⊥ₗ, gA, gB, gC, gD, gK]) nD (by simp) (by simp)))))))

theorem lStep : [InvR] ⊢ [𝐗 InvR] :=
  .andL (A := PosI) (B := Gs) (by simp)
  (.andL (A := gA) (B := gB ⋏ (gC ⋏ (gD ⋏ gK))) (by simp)
  (.andL (A := gB) (B := gC ⋏ (gD ⋏ gK)) (by simp)
  (.andL (A := gC) (B := gD ⋏ gK) (by simp)
  (.andL (A := gD) (B := gK) (by simp)
  (.orL (A := at_ cA) (B := at_ cB ⋎ (at_ cC ⋎ at_ cDock)) (by simp)
    (.wk sA (by simp) (by simp))
  (.orL (A := at_ cB) (B := at_ cC ⋎ at_ cDock) (by simp)
    (.wk sB (by simp) (by simp))
  (.orL (A := at_ cC) (B := at_ cDock) (by simp)
    (.wk sC (by simp) (by simp))
    (.wk sD (by simp) (by simp)))))))))

theorem candidate : S.hyps ⊢ [lift specRecur] := by
  show [(at_ cA ⋎ ⊥ₗ), 𝐆 (at_ cA ⇒ ∼(ap dock)), 𝐆 (at_ cA ⇒ ∼(ap hazard)), 𝐆 (at_ cA ⇒ ∼(ap low)), 𝐆 (at_ cA ⇒ 𝐗 (at_ cB ⋎ (at_ cC ⋎ ⊥ₗ))), 𝐆 (at_ cB ⇒ ap low), 𝐆 (at_ cB ⇒ ∼(ap dock)), 𝐆 (at_ cB ⇒ ∼(ap hazard)), 𝐆 (at_ cB ⇒ 𝐗 (at_ cC ⋎ ⊥ₗ)), 𝐆 (at_ cC ⇒ ∼(ap dock)), 𝐆 (at_ cC ⇒ ∼(ap hazard)), 𝐆 (at_ cC ⇒ ∼(ap low)), 𝐆 (at_ cC ⇒ 𝐗 (at_ cDock ⋎ ⊥ₗ)), 𝐆 (at_ cDock ⇒ ap dock), 𝐆 (at_ cDock ⇒ ∼(ap hazard)), 𝐆 (at_ cDock ⇒ ∼(ap low)), 𝐆 (at_ cDock ⇒ 𝐗 (at_ cA ⋎ ⊥ₗ)), 𝐆 (at_ cHaz ⇒ ap hazard), 𝐆 (at_ cHaz ⇒ ∼(ap dock)), 𝐆 (at_ cHaz ⇒ ∼(ap low)), 𝐆 (at_ cHaz ⇒ 𝐗 (at_ cHaz ⋎ ⊥ₗ))] ⊢ [𝐆 𝐅 (ap dock)]
  exact .alwaysR (A := 𝐅 (ap dock)) (I := InvR) (by simp)
    (.wk nD (by simp) (by simp)) lStep lGoal

end Candidate

theorem verified : Bench.Robot.S.Models Bench.Robot.specRecur :=
  Bench.Robot.S.sat_of_derives Candidate.candidate

#print axioms verified
