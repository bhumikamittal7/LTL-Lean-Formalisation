import Bench

open LTL LTL.System
open Bench.Wait
open Bench.Wait.P Bench.Wait.St

namespace Candidate

abbrev A0 : Formula (P ⊕ St) := at_ q0 ⋎ ⊥ₗ
abbrev A1 : Formula (P ⊕ St) := at_ q1 ⋎ ⊥ₗ
abbrev G3 : Formula (P ⊕ St) := 𝐆 (at_ q0 ⇒ 𝐗 A1)
abbrev G4 : Formula (P ⊕ St) := 𝐆 (at_ q1 ⇒ ap done)
abbrev G5 : Formula (P ⊕ St) := 𝐆 (at_ q1 ⇒ ∼(ap wait))
abbrev G6 : Formula (P ⊕ St) := 𝐆 (at_ q1 ⇒ 𝐗 A1)
abbrev Hs : Formula (P ⊕ St) := G3 ⋏ (G4 ⋏ (G5 ⋏ G6))
abbrev Inv : Formula (P ⊕ St) := (A0 ⋎ A1) ⋏ Hs

theorem candidate : S.hyps ⊢ [lift specNext] := by
  show [(at_ q0 ⋎ ⊥ₗ), 𝐆 (at_ q0 ⇒ ap wait), 𝐆 (at_ q0 ⇒ ∼(ap done)), 𝐆 (at_ q0 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ)), 𝐆 (at_ q1 ⇒ ap done), 𝐆 (at_ q1 ⇒ ∼(ap wait)), 𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ))] ⊢ [𝐆 (ap wait ⇒ 𝐗 (ap done))]
  have hP : [A1, G3, G4, G5, G6] ⊢ [Inv] :=
    .andR (A := A0 ⋎ A1) (B := Hs) (by simp)
      (.orR (A := A0) (B := A1) (by simp) (.close (by decide)))
      (.andR (A := G3) (B := G4 ⋏ (G5 ⋏ G6)) (by simp) (.close (by decide))
        (.andR (A := G4) (B := G5 ⋏ G6) (by simp) (.close (by decide))
          (.andR (A := G5) (B := G6) (by simp) (.close (by decide)) (.close (by decide)))))
  have hQ : [A1, G4] ⊢ [ap done] :=
    .alwaysL (A := at_ q1 ⇒ ap done) (by simp)
      (.orL (A := at_ q1) (B := ⊥ₗ) (by simp)
        (.impL (A := at_ q1) (B := ap done) (by simp) (.close (by decide)) (.close (by decide)))
        (.botL (by simp)))
  have h1 : [(at_ q0 ⋎ ⊥ₗ), 𝐆 (at_ q0 ⇒ ap wait), 𝐆 (at_ q0 ⇒ ∼(ap done)), 𝐆 (at_ q0 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ)), 𝐆 (at_ q1 ⇒ ap done), 𝐆 (at_ q1 ⇒ ∼(ap wait)), 𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ))] ⊢ [Inv, 𝐆 (ap wait ⇒ 𝐗 (ap done))] :=
    .andR (A := A0 ⋎ A1) (B := Hs) (by simp)
      (.orR (A := A0) (B := A1) (by simp) (.close (by decide)))
      (.andR (A := G3) (B := G4 ⋏ (G5 ⋏ G6)) (by simp) (.close (by decide))
        (.andR (A := G4) (B := G5 ⋏ G6) (by simp) (.close (by decide))
          (.andR (A := G5) (B := G6) (by simp) (.close (by decide)) (.close (by decide)))))
  have hNext : [A0 ⋎ A1, G3, G4, G5, G6] ⊢ [𝐗 Inv] :=
    .alwaysL (A := at_ q0 ⇒ 𝐗 A1) (by simp)
      (.alwaysL (A := at_ q1 ⇒ ap done) (by simp)
        (.alwaysL (A := at_ q1 ⇒ ∼(ap wait)) (by simp)
          (.alwaysL (A := at_ q1 ⇒ 𝐗 A1) (by simp)
            (.orL (A := A0) (B := A1) (by simp)
              (.orL (A := at_ q0) (B := ⊥ₗ) (by simp)
                (.impL (A := at_ q0) (B := 𝐗 A1) (by simp) (.close (by decide))
                  (Derives.step (Γ' := [A1, G3, G4, G5, G6]) (B := Inv) hP (by simp) (by simp)))
                (.botL (by simp)))
              (.orL (A := at_ q1) (B := ⊥ₗ) (by simp)
                (.impL (A := at_ q1) (B := 𝐗 A1) (by simp) (.close (by decide))
                  (Derives.step (Γ' := [A1, G3, G4, G5, G6]) (B := Inv) hP (by simp) (by simp)))
                (.botL (by simp)))))))
  have h2 : [Inv] ⊢ [𝐗 Inv] :=
    .andL (A := A0 ⋎ A1) (B := Hs) (by simp)
      (.andL (A := G3) (B := G4 ⋏ (G5 ⋏ G6)) (by simp)
        (.andL (A := G4) (B := G5 ⋏ G6) (by simp)
          (.andL (A := G5) (B := G6) (by simp)
            (Derives.wk hNext (by simp) (by simp)))))
  have hGoal : [A0 ⋎ A1, G3, G4, G5] ⊢ [ap wait ⇒ 𝐗 (ap done)] :=
    .impR (A := ap wait) (B := 𝐗 (ap done)) (by simp)
      (.alwaysL (A := at_ q0 ⇒ 𝐗 A1) (by simp)
        (.alwaysL (A := at_ q1 ⇒ ap done) (by simp)
          (.alwaysL (A := at_ q1 ⇒ ∼(ap wait)) (by simp)
            (.orL (A := A0) (B := A1) (by simp)
              (.orL (A := at_ q0) (B := ⊥ₗ) (by simp)
                (.impL (A := at_ q0) (B := 𝐗 A1) (by simp) (.close (by decide))
                  (Derives.step (Γ' := [A1, G4]) (B := ap done) hQ (by simp) (by simp)))
                (.botL (by simp)))
              (.orL (A := at_ q1) (B := ⊥ₗ) (by simp)
                (.impL (A := at_ q1) (B := ∼(ap wait)) (by simp) (.close (by decide))
                  (.negL (A := ap wait) (by simp) (.close (by decide))))
                (.botL (by simp)))))))
  have h3 : [Inv] ⊢ [ap wait ⇒ 𝐗 (ap done)] :=
    .andL (A := A0 ⋎ A1) (B := Hs) (by simp)
      (.andL (A := G3) (B := G4 ⋏ (G5 ⋏ G6)) (by simp)
        (.andL (A := G4) (B := G5 ⋏ G6) (by simp)
          (.andL (A := G5) (B := G6) (by simp)
            (Derives.wk hGoal (by simp) (by simp)))))
  exact .alwaysR (A := ap wait ⇒ 𝐗 (ap done)) Inv (by simp) h1 h2 h3

end Candidate

theorem verified : Bench.Wait.S.Models Bench.Wait.specNext :=
  Bench.Wait.S.sat_of_derives Candidate.candidate

#print axioms verified
