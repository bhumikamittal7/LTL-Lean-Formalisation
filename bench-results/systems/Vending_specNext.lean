import Bench

open LTL LTL.System
open Bench.Vending
open Bench.Vending.P Bench.Vending.St

namespace Candidate

abbrev vG1 : Formula (P ⊕ St) := 𝐆 (at_ pay ⇒ ∼(ap paid))
abbrev vG2 : Formula (P ⊕ St) := 𝐆 (at_ pay ⇒ ∼(ap drink))
abbrev vG3 : Formula (P ⊕ St) := 𝐆 (at_ pay ⇒ 𝐗 (at_ select ⋎ ⊥ₗ))
abbrev vG5 : Formula (P ⊕ St) := 𝐆 (at_ select ⇒ ∼(ap drink))
abbrev vG6 : Formula (P ⊕ St) := 𝐆 (at_ select ⇒ 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ)))
abbrev vG9 : Formula (P ⊕ St) := 𝐆 (at_ soda ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ))
abbrev vG12 : Formula (P ⊕ St) := 𝐆 (at_ beer ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ))

abbrev vQR3 : Formula (P ⊕ St) := at_ beer ⋎ ⊥ₗ
abbrev vQR2 : Formula (P ⊕ St) := at_ soda ⋎ vQR3
abbrev vQR1 : Formula (P ⊕ St) := at_ select ⋎ vQR2
abbrev vQ : Formula (P ⊕ St) := at_ pay ⋎ vQR1

abbrev vR6 : Formula (P ⊕ St) := vG9 ⋏ vG12
abbrev vR5 : Formula (P ⊕ St) := vG6 ⋏ vR6
abbrev vR4 : Formula (P ⊕ St) := vG5 ⋏ vR5
abbrev vR3 : Formula (P ⊕ St) := vG3 ⋏ vR4
abbrev vR2 : Formula (P ⊕ St) := vG2 ⋏ vR3
abbrev vR1 : Formula (P ⊕ St) := vG1 ⋏ vR2
abbrev vI : Formula (P ⊕ St) := vQ ⋏ vR1

theorem vm_qPay {Γ Δ : List (Formula (P ⊕ St))} (h : (at_ pay ⋎ ⊥ₗ) ∈ Γ) :
    Γ ⊢ (vQ :: Δ) :=
  .orL (A := at_ pay) (B := ⊥ₗ) h
    (.orR (A := at_ pay) (B := vQR1) (by simp) (.ax (A := at_ pay) (by simp) (by simp)))
    (.botL (by simp))

theorem vm_qSel {Γ Δ : List (Formula (P ⊕ St))} (h : (at_ select ⋎ ⊥ₗ) ∈ Γ) :
    Γ ⊢ (vQ :: Δ) :=
  .orL (A := at_ select) (B := ⊥ₗ) h
    (.orR (A := at_ pay) (B := vQR1) (by simp) <|
      .orR (A := at_ select) (B := vQR2) (by simp) <|
      .ax (A := at_ select) (by simp) (by simp))
    (.botL (by simp))

theorem vm_qSB {Γ Δ : List (Formula (P ⊕ St))} (h : (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ)) ∈ Γ) :
    Γ ⊢ (vQ :: Δ) :=
  .orL (A := at_ soda) (B := vQR3) h
    (.orR (A := at_ pay) (B := vQR1) (by simp) <|
      .orR (A := at_ select) (B := vQR2) (by simp) <|
      .orR (A := at_ soda) (B := vQR3) (by simp) <|
      .ax (A := at_ soda) (by simp) (by simp))
    (.orL (A := at_ beer) (B := ⊥ₗ) (by simp)
      (.orR (A := at_ pay) (B := vQR1) (by simp) <|
        .orR (A := at_ select) (B := vQR2) (by simp) <|
        .orR (A := at_ soda) (B := vQR3) (by simp) <|
        .orR (A := at_ beer) (B := ⊥ₗ) (by simp) <|
        .ax (A := at_ beer) (by simp) (by simp))
      (.botL (by simp)))

theorem vm_inv_intro {Γ Δ : List (Formula (P ⊕ St))}
    (hQ : Γ ⊢ (vQ :: vI :: Δ)) (h1 : vG1 ∈ Γ) (h2 : vG2 ∈ Γ) (h3 : vG3 ∈ Γ)
    (h5 : vG5 ∈ Γ) (h6 : vG6 ∈ Γ) (h9 : vG9 ∈ Γ) (h12 : vG12 ∈ Γ) :
    Γ ⊢ (vI :: Δ) :=
  .andR (A := vQ) (B := vR1) (by simp) hQ <|
  .andR (A := vG1) (B := vR2) (by simp) (.ax (A := vG1) h1 (by simp)) <|
  .andR (A := vG2) (B := vR3) (by simp) (.ax (A := vG2) h2 (by simp)) <|
  .andR (A := vG3) (B := vR4) (by simp) (.ax (A := vG3) h3 (by simp)) <|
  .andR (A := vG5) (B := vR5) (by simp) (.ax (A := vG5) h5 (by simp)) <|
  .andR (A := vG6) (B := vR6) (by simp) (.ax (A := vG6) h6 (by simp)) <|
  .andR (A := vG9) (B := vG12) (by simp) (.ax (A := vG9) h9 (by simp))
    (.ax (A := vG12) h12 (by simp))

theorem vm_stepInv : [vI] ⊢ [𝐗 vI] :=
  .andL (A := vQ) (B := vR1) (by simp) <|
  .andL (A := vG1) (B := vR2) (by simp) <|
  .andL (A := vG2) (B := vR3) (by simp) <|
  .andL (A := vG3) (B := vR4) (by simp) <|
  .andL (A := vG5) (B := vR5) (by simp) <|
  .andL (A := vG6) (B := vR6) (by simp) <|
  .andL (A := vG9) (B := vG12) (by simp) <|
  .alwaysL (A := at_ pay ⇒ 𝐗 (at_ select ⋎ ⊥ₗ)) (by simp) <|
  .alwaysL (A := at_ select ⇒ 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))) (by simp) <|
  .alwaysL (A := at_ soda ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ)) (by simp) <|
  .alwaysL (A := at_ beer ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ)) (by simp) <|
  .alwaysL (A := at_ pay ⇒ ∼(ap paid)) (by simp) <|
  .alwaysL (A := at_ pay ⇒ ∼(ap drink)) (by simp) <|
  .alwaysL (A := at_ select ⇒ ∼(ap drink)) (by simp) <|
  .orL (A := at_ pay) (B := vQR1) (by simp)
    (.impL (A := at_ pay) (B := 𝐗 (at_ select ⋎ ⊥ₗ)) (by simp)
      (.ax (A := at_ pay) (by simp) (by simp))
      (.step (Γ' := [at_ select ⋎ ⊥ₗ, vG1, vG2, vG3, vG5, vG6, vG9, vG12])
        (vm_inv_intro (vm_qSel (by simp)) (by simp) (by simp) (by simp) (by simp)
          (by simp) (by simp) (by simp))
        (by simp) (by simp)))
    (.orL (A := at_ select) (B := vQR2) (by simp)
      (.impL (A := at_ select) (B := 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))) (by simp)
        (.ax (A := at_ select) (by simp) (by simp))
        (.step (Γ' := [at_ soda ⋎ (at_ beer ⋎ ⊥ₗ), vG1, vG2, vG3, vG5, vG6, vG9, vG12])
          (vm_inv_intro (vm_qSB (by simp)) (by simp) (by simp) (by simp) (by simp)
            (by simp) (by simp) (by simp))
          (by simp) (by simp)))
      (.orL (A := at_ soda) (B := vQR3) (by simp)
        (.impL (A := at_ soda) (B := 𝐗 (at_ pay ⋎ ⊥ₗ)) (by simp)
          (.ax (A := at_ soda) (by simp) (by simp))
          (.step (Γ' := [at_ pay ⋎ ⊥ₗ, vG1, vG2, vG3, vG5, vG6, vG9, vG12])
            (vm_inv_intro (vm_qPay (by simp)) (by simp) (by simp) (by simp) (by simp)
              (by simp) (by simp) (by simp))
            (by simp) (by simp)))
        (.orL (A := at_ beer) (B := ⊥ₗ) (by simp)
          (.impL (A := at_ beer) (B := 𝐗 (at_ pay ⋎ ⊥ₗ)) (by simp)
            (.ax (A := at_ beer) (by simp) (by simp))
            (.step (Γ' := [at_ pay ⋎ ⊥ₗ, vG1, vG2, vG3, vG5, vG6, vG9, vG12])
              (vm_inv_intro (vm_qPay (by simp)) (by simp) (by simp) (by simp) (by simp)
                (by simp) (by simp) (by simp))
              (by simp) (by simp)))
          (.botL (by simp)))))

theorem vm_nextPaid : [at_ pay ⋎ ⊥ₗ, vG1] ⊢ [∼(ap paid)] :=
  .alwaysL (A := at_ pay ⇒ ∼(ap paid)) (by simp) <|
  .orL (A := at_ pay) (B := ⊥ₗ) (by simp)
    (.impL (A := at_ pay) (B := ∼(ap paid)) (by simp)
      (.ax (A := at_ pay) (by simp) (by simp))
      (.ax (A := ∼(ap paid)) (by simp) (by simp)))
    (.botL (by simp))

theorem vm_goalInv : [vI] ⊢ [ap drink ⇒ 𝐗 (∼(ap paid))] :=
  .andL (A := vQ) (B := vR1) (by simp) <|
  .andL (A := vG1) (B := vR2) (by simp) <|
  .andL (A := vG2) (B := vR3) (by simp) <|
  .andL (A := vG3) (B := vR4) (by simp) <|
  .andL (A := vG5) (B := vR5) (by simp) <|
  .andL (A := vG6) (B := vR6) (by simp) <|
  .andL (A := vG9) (B := vG12) (by simp) <|
  .alwaysL (A := at_ pay ⇒ ∼(ap paid)) (by simp) <|
  .alwaysL (A := at_ pay ⇒ ∼(ap drink)) (by simp) <|
  .alwaysL (A := at_ select ⇒ ∼(ap drink)) (by simp) <|
  .alwaysL (A := at_ soda ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ)) (by simp) <|
  .alwaysL (A := at_ beer ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ)) (by simp) <|
  .impR (A := ap drink) (B := 𝐗 (∼(ap paid))) (by simp) <|
  .orL (A := at_ pay) (B := vQR1) (by simp)
    (.impL (A := at_ pay) (B := ∼(ap drink)) (by simp)
      (.ax (A := at_ pay) (by simp) (by simp))
      (.negL (A := ap drink) (by simp) (.ax (A := ap drink) (by simp) (by simp))))
    (.orL (A := at_ select) (B := vQR2) (by simp)
      (.impL (A := at_ select) (B := ∼(ap drink)) (by simp)
        (.ax (A := at_ select) (by simp) (by simp))
        (.negL (A := ap drink) (by simp) (.ax (A := ap drink) (by simp) (by simp))))
      (.orL (A := at_ soda) (B := vQR3) (by simp)
        (.impL (A := at_ soda) (B := 𝐗 (at_ pay ⋎ ⊥ₗ)) (by simp)
          (.ax (A := at_ soda) (by simp) (by simp))
          (.step (Γ' := [at_ pay ⋎ ⊥ₗ, vG1]) vm_nextPaid (by simp) (by simp)))
        (.orL (A := at_ beer) (B := ⊥ₗ) (by simp)
          (.impL (A := at_ beer) (B := 𝐗 (at_ pay ⋎ ⊥ₗ)) (by simp)
            (.ax (A := at_ beer) (by simp) (by simp))
            (.step (Γ' := [at_ pay ⋎ ⊥ₗ, vG1]) vm_nextPaid (by simp) (by simp)))
          (.botL (by simp)))))

theorem candidate : S.hyps ⊢ [lift specNext] := by
  show [(at_ pay ⋎ ⊥ₗ), 𝐆 (at_ pay ⇒ ∼(ap paid)), 𝐆 (at_ pay ⇒ ∼(ap drink)), 𝐆 (at_ pay ⇒ 𝐗 (at_ select ⋎ ⊥ₗ)), 𝐆 (at_ select ⇒ ap paid), 𝐆 (at_ select ⇒ ∼(ap drink)), 𝐆 (at_ select ⇒ 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))), 𝐆 (at_ soda ⇒ ap paid), 𝐆 (at_ soda ⇒ ap drink), 𝐆 (at_ soda ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ)), 𝐆 (at_ beer ⇒ ap paid), 𝐆 (at_ beer ⇒ ap drink), 𝐆 (at_ beer ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ))] ⊢ [𝐆 (ap drink ⇒ 𝐗 (∼(ap paid)))]
  exact .alwaysR (A := ap drink ⇒ 𝐗 (∼(ap paid))) vI (by simp)
    (vm_inv_intro (vm_qPay (by simp)) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp))
    vm_stepInv vm_goalInv

end Candidate

theorem verified : Bench.Vending.S.Models Bench.Vending.specNext :=
  Bench.Vending.S.sat_of_derives Candidate.candidate

#print axioms verified
