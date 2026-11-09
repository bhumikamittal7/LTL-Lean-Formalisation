import Bench

open LTL LTL.System
open Bench.Peterson
open Bench.Peterson.P Bench.Peterson.St

namespace Candidate

abbrev RA8 : Formula (P ⊕ St) := at_ cw1 ⋎ at_ wc2
abbrev RA7 : Formula (P ⊕ St) := at_ nc1 ⋎ RA8
abbrev RA6 : Formula (P ⊕ St) := at_ ww2 ⋎ RA7
abbrev RA5 : Formula (P ⊕ St) := at_ ww1 ⋎ RA6
abbrev RA4 : Formula (P ⊕ St) := at_ cn2 ⋎ RA5
abbrev RA3 : Formula (P ⊕ St) := at_ wn2 ⋎ RA4
abbrev RA2 : Formula (P ⊕ St) := at_ nw1 ⋎ RA3
abbrev RA1 : Formula (P ⊕ St) := at_ nn2 ⋎ RA2
abbrev RA0 : Formula (P ⊕ St) := at_ nn1 ⋎ RA1

abbrev SA1 : Formula (P ⊕ St) := at_ nn1 ⇒ ∼(ap crit1)
abbrev SA2 : Formula (P ⊕ St) := at_ nn2 ⇒ ∼(ap crit1)
abbrev SA3 : Formula (P ⊕ St) := at_ nw1 ⇒ ∼(ap crit1)
abbrev SA4 : Formula (P ⊕ St) := at_ wn2 ⇒ ∼(ap crit1)
abbrev SA5 : Formula (P ⊕ St) := at_ cn2 ⇒ ∼(ap crit2)
abbrev SA6 : Formula (P ⊕ St) := at_ ww1 ⇒ ∼(ap crit1)
abbrev SA7 : Formula (P ⊕ St) := at_ ww2 ⇒ ∼(ap crit1)
abbrev SA8 : Formula (P ⊕ St) := at_ nc1 ⇒ ∼(ap crit1)
abbrev SA9 : Formula (P ⊕ St) := at_ cw1 ⇒ ∼(ap crit2)
abbrev SA10 : Formula (P ⊕ St) := at_ wc2 ⇒ ∼(ap crit1)

abbrev TA1 : Formula (P ⊕ St) := at_ nn1 ⇒ 𝐗 (at_ wn2 ⋎ (at_ nw1 ⋎ ⊥ₗ))
abbrev TA2 : Formula (P ⊕ St) := at_ nn2 ⇒ 𝐗 (at_ wn2 ⋎ (at_ nw1 ⋎ ⊥ₗ))
abbrev TA3 : Formula (P ⊕ St) := at_ nw1 ⇒ 𝐗 (at_ ww2 ⋎ (at_ nc1 ⋎ ⊥ₗ))
abbrev TA4 : Formula (P ⊕ St) := at_ wn2 ⇒ 𝐗 (at_ cn2 ⋎ (at_ ww1 ⋎ ⊥ₗ))
abbrev TA5 : Formula (P ⊕ St) := at_ cn2 ⇒ 𝐗 (at_ nn2 ⋎ (at_ cw1 ⋎ ⊥ₗ))
abbrev TA6 : Formula (P ⊕ St) := at_ ww1 ⇒ 𝐗 (at_ cw1 ⋎ ⊥ₗ)
abbrev TA7 : Formula (P ⊕ St) := at_ ww2 ⇒ 𝐗 (at_ wc2 ⋎ ⊥ₗ)
abbrev TA8 : Formula (P ⊕ St) := at_ nc1 ⇒ 𝐗 (at_ wc2 ⋎ (at_ nn1 ⋎ ⊥ₗ))
abbrev TA9 : Formula (P ⊕ St) := at_ cw1 ⇒ 𝐗 (at_ nw1 ⋎ ⊥ₗ)
abbrev TA10 : Formula (P ⊕ St) := at_ wc2 ⇒ 𝐗 (at_ wn2 ⋎ ⊥ₗ)

abbrev KA19 : Formula (P ⊕ St) := 𝐆 TA10
abbrev KA18 : Formula (P ⊕ St) := (𝐆 TA9) ⋏ KA19
abbrev KA17 : Formula (P ⊕ St) := (𝐆 TA8) ⋏ KA18
abbrev KA16 : Formula (P ⊕ St) := (𝐆 TA7) ⋏ KA17
abbrev KA15 : Formula (P ⊕ St) := (𝐆 TA6) ⋏ KA16
abbrev KA14 : Formula (P ⊕ St) := (𝐆 TA5) ⋏ KA15
abbrev KA13 : Formula (P ⊕ St) := (𝐆 TA4) ⋏ KA14
abbrev KA12 : Formula (P ⊕ St) := (𝐆 TA3) ⋏ KA13
abbrev KA11 : Formula (P ⊕ St) := (𝐆 TA2) ⋏ KA12
abbrev KA10 : Formula (P ⊕ St) := (𝐆 TA1) ⋏ KA11
abbrev KA9 : Formula (P ⊕ St) := (𝐆 SA10) ⋏ KA10
abbrev KA8 : Formula (P ⊕ St) := (𝐆 SA9) ⋏ KA9
abbrev KA7 : Formula (P ⊕ St) := (𝐆 SA8) ⋏ KA8
abbrev KA6 : Formula (P ⊕ St) := (𝐆 SA7) ⋏ KA7
abbrev KA5 : Formula (P ⊕ St) := (𝐆 SA6) ⋏ KA6
abbrev KA4 : Formula (P ⊕ St) := (𝐆 SA5) ⋏ KA5
abbrev KA3 : Formula (P ⊕ St) := (𝐆 SA4) ⋏ KA4
abbrev KA2 : Formula (P ⊕ St) := (𝐆 SA3) ⋏ KA3
abbrev KA1 : Formula (P ⊕ St) := (𝐆 SA2) ⋏ KA2
abbrev KA0 : Formula (P ⊕ St) := (𝐆 SA1) ⋏ KA1

abbrev mxInv : Formula (P ⊕ St) := RA0 ⋏ KA0

theorem mxExpR (Γ : List (Formula (P ⊕ St)))
    (h : Γ ⊢ [at_ nn1, at_ nn2, at_ nw1, at_ wn2, at_ cn2, at_ ww1, at_ ww2, at_ nc1, at_ cw1, at_ wc2]) :
    Γ ⊢ [RA0] :=
  .orR (A := at_ nn1) (B := RA1) (by simp) <|
  .orR (A := at_ nn2) (B := RA2) (by simp) <|
  .orR (A := at_ nw1) (B := RA3) (by simp) <|
  .orR (A := at_ wn2) (B := RA4) (by simp) <|
  .orR (A := at_ cn2) (B := RA5) (by simp) <|
  .orR (A := at_ ww1) (B := RA6) (by simp) <|
  .orR (A := at_ ww2) (B := RA7) (by simp) <|
  .orR (A := at_ nc1) (B := RA8) (by simp) <|
  .orR (A := at_ cw1) (B := at_ wc2) (by simp) <|
  .wk h (fun _ hx => hx) (by simp)

theorem mxSc2 (a b : Formula (P ⊕ St))
    (ha : a ∈ [at_ nn1, at_ nn2, at_ nw1, at_ wn2, at_ cn2, at_ ww1, at_ ww2, at_ nc1, at_ cw1, at_ wc2])
    (hb : b ∈ [at_ nn1, at_ nn2, at_ nw1, at_ wn2, at_ cn2, at_ ww1, at_ ww2, at_ nc1, at_ cw1, at_ wc2]) :
    [a ⋎ (b ⋎ ⊥ₗ)] ⊢ [RA0] :=
  mxExpR _ (.orL (A := a) (B := b ⋎ ⊥ₗ) (by simp)
    (.ax (A := a) (by simp) ha)
    (.orL (A := b) (B := ⊥ₗ) (by simp) (.ax (A := b) (by simp) hb) (.botL (by simp))))

theorem mxSc1 (a : Formula (P ⊕ St))
    (ha : a ∈ [at_ nn1, at_ nn2, at_ nw1, at_ wn2, at_ cn2, at_ ww1, at_ ww2, at_ nc1, at_ cw1, at_ wc2]) :
    [a ⋎ ⊥ₗ] ⊢ [RA0] :=
  mxExpR _ (.orL (A := a) (B := ⊥ₗ) (by simp) (.ax (A := a) (by simp) ha) (.botL (by simp)))

theorem mxP1 : [at_ nn1 ⋎ (at_ nn2 ⋎ ⊥ₗ), 𝐆 SA1, 𝐆 SA2, 𝐆 SA3, 𝐆 SA4, 𝐆 SA5, 𝐆 SA6, 𝐆 SA7, 𝐆 SA8, 𝐆 SA9, 𝐆 SA10,
    𝐆 TA1, 𝐆 TA2, 𝐆 TA3, 𝐆 TA4, 𝐆 TA5, 𝐆 TA6, 𝐆 TA7, 𝐆 TA8, 𝐆 TA9, 𝐆 TA10]
    ⊢ [mxInv, 𝐆 (∼(ap crit1 ⋏ ap crit2))] :=
  .andR (A := RA0) (B := KA0) (by simp)
    (.wk (mxSc2 (at_ nn1) (at_ nn2) (by simp) (by simp)) (by simp) (by simp)) <|
  .andR (A := 𝐆 SA1) (B := KA1) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 SA2) (B := KA2) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 SA3) (B := KA3) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 SA4) (B := KA4) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 SA5) (B := KA5) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 SA6) (B := KA6) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 SA7) (B := KA7) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 SA8) (B := KA8) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 SA9) (B := KA9) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 SA10) (B := KA10) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 TA1) (B := KA11) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 TA2) (B := KA12) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 TA3) (B := KA13) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 TA4) (B := KA14) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 TA5) (B := KA15) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 TA6) (B := KA16) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 TA7) (B := KA17) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 TA8) (B := KA18) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 TA9) (B := KA19) (by simp) (.close (by decide)) <|
  .close (by decide)

set_option maxHeartbeats 4000000 in
theorem mxP2 : [mxInv] ⊢ [𝐗 mxInv] :=
  .andL (A := RA0) (B := KA0) (by simp) <|
  .andL (A := 𝐆 SA1) (B := KA1) (by simp) <|
  .andL (A := 𝐆 SA2) (B := KA2) (by simp) <|
  .andL (A := 𝐆 SA3) (B := KA3) (by simp) <|
  .andL (A := 𝐆 SA4) (B := KA4) (by simp) <|
  .andL (A := 𝐆 SA5) (B := KA5) (by simp) <|
  .andL (A := 𝐆 SA6) (B := KA6) (by simp) <|
  .andL (A := 𝐆 SA7) (B := KA7) (by simp) <|
  .andL (A := 𝐆 SA8) (B := KA8) (by simp) <|
  .andL (A := 𝐆 SA9) (B := KA9) (by simp) <|
  .andL (A := 𝐆 SA10) (B := KA10) (by simp) <|
  .andL (A := 𝐆 TA1) (B := KA11) (by simp) <|
  .andL (A := 𝐆 TA2) (B := KA12) (by simp) <|
  .andL (A := 𝐆 TA3) (B := KA13) (by simp) <|
  .andL (A := 𝐆 TA4) (B := KA14) (by simp) <|
  .andL (A := 𝐆 TA5) (B := KA15) (by simp) <|
  .andL (A := 𝐆 TA6) (B := KA16) (by simp) <|
  .andL (A := 𝐆 TA7) (B := KA17) (by simp) <|
  .andL (A := 𝐆 TA8) (B := KA18) (by simp) <|
  .andL (A := 𝐆 TA9) (B := KA19) (by simp) <|
  .alwaysL (A := SA1) (by simp) <|
  .alwaysL (A := SA2) (by simp) <|
  .alwaysL (A := SA3) (by simp) <|
  .alwaysL (A := SA4) (by simp) <|
  .alwaysL (A := SA5) (by simp) <|
  .alwaysL (A := SA6) (by simp) <|
  .alwaysL (A := SA7) (by simp) <|
  .alwaysL (A := SA8) (by simp) <|
  .alwaysL (A := SA9) (by simp) <|
  .alwaysL (A := SA10) (by simp) <|
  .alwaysL (A := TA1) (by simp) <|
  .alwaysL (A := TA2) (by simp) <|
  .alwaysL (A := TA3) (by simp) <|
  .alwaysL (A := TA4) (by simp) <|
  .alwaysL (A := TA5) (by simp) <|
  .alwaysL (A := TA6) (by simp) <|
  .alwaysL (A := TA7) (by simp) <|
  .alwaysL (A := TA8) (by simp) <|
  .alwaysL (A := TA9) (by simp) <|
  .alwaysL (A := TA10) (by simp) <|
  .cut (A := 𝐗 RA0)
    (.orL (A := at_ nn1) (B := RA1) (by simp)
      (.impL (A := at_ nn1) (B := 𝐗 (at_ wn2 ⋎ (at_ nw1 ⋎ ⊥ₗ))) (by simp) (.close (by decide))
        (.step (Γ' := [at_ wn2 ⋎ (at_ nw1 ⋎ ⊥ₗ)]) (B := RA0)
          (mxSc2 (at_ wn2) (at_ nw1) (by simp) (by simp)) (by simp) (by simp))) <|
     .orL (A := at_ nn2) (B := RA2) (by simp)
      (.impL (A := at_ nn2) (B := 𝐗 (at_ wn2 ⋎ (at_ nw1 ⋎ ⊥ₗ))) (by simp) (.close (by decide))
        (.step (Γ' := [at_ wn2 ⋎ (at_ nw1 ⋎ ⊥ₗ)]) (B := RA0)
          (mxSc2 (at_ wn2) (at_ nw1) (by simp) (by simp)) (by simp) (by simp))) <|
     .orL (A := at_ nw1) (B := RA3) (by simp)
      (.impL (A := at_ nw1) (B := 𝐗 (at_ ww2 ⋎ (at_ nc1 ⋎ ⊥ₗ))) (by simp) (.close (by decide))
        (.step (Γ' := [at_ ww2 ⋎ (at_ nc1 ⋎ ⊥ₗ)]) (B := RA0)
          (mxSc2 (at_ ww2) (at_ nc1) (by simp) (by simp)) (by simp) (by simp))) <|
     .orL (A := at_ wn2) (B := RA4) (by simp)
      (.impL (A := at_ wn2) (B := 𝐗 (at_ cn2 ⋎ (at_ ww1 ⋎ ⊥ₗ))) (by simp) (.close (by decide))
        (.step (Γ' := [at_ cn2 ⋎ (at_ ww1 ⋎ ⊥ₗ)]) (B := RA0)
          (mxSc2 (at_ cn2) (at_ ww1) (by simp) (by simp)) (by simp) (by simp))) <|
     .orL (A := at_ cn2) (B := RA5) (by simp)
      (.impL (A := at_ cn2) (B := 𝐗 (at_ nn2 ⋎ (at_ cw1 ⋎ ⊥ₗ))) (by simp) (.close (by decide))
        (.step (Γ' := [at_ nn2 ⋎ (at_ cw1 ⋎ ⊥ₗ)]) (B := RA0)
          (mxSc2 (at_ nn2) (at_ cw1) (by simp) (by simp)) (by simp) (by simp))) <|
     .orL (A := at_ ww1) (B := RA6) (by simp)
      (.impL (A := at_ ww1) (B := 𝐗 (at_ cw1 ⋎ ⊥ₗ)) (by simp) (.close (by decide))
        (.step (Γ' := [at_ cw1 ⋎ ⊥ₗ]) (B := RA0)
          (mxSc1 (at_ cw1) (by simp)) (by simp) (by simp))) <|
     .orL (A := at_ ww2) (B := RA7) (by simp)
      (.impL (A := at_ ww2) (B := 𝐗 (at_ wc2 ⋎ ⊥ₗ)) (by simp) (.close (by decide))
        (.step (Γ' := [at_ wc2 ⋎ ⊥ₗ]) (B := RA0)
          (mxSc1 (at_ wc2) (by simp)) (by simp) (by simp))) <|
     .orL (A := at_ nc1) (B := RA8) (by simp)
      (.impL (A := at_ nc1) (B := 𝐗 (at_ wc2 ⋎ (at_ nn1 ⋎ ⊥ₗ))) (by simp) (.close (by decide))
        (.step (Γ' := [at_ wc2 ⋎ (at_ nn1 ⋎ ⊥ₗ)]) (B := RA0)
          (mxSc2 (at_ wc2) (at_ nn1) (by simp) (by simp)) (by simp) (by simp))) <|
     .orL (A := at_ cw1) (B := at_ wc2) (by simp)
      (.impL (A := at_ cw1) (B := 𝐗 (at_ nw1 ⋎ ⊥ₗ)) (by simp) (.close (by decide))
        (.step (Γ' := [at_ nw1 ⋎ ⊥ₗ]) (B := RA0)
          (mxSc1 (at_ nw1) (by simp)) (by simp) (by simp)))
      (.impL (A := at_ wc2) (B := 𝐗 (at_ wn2 ⋎ ⊥ₗ)) (by simp) (.close (by decide))
        (.step (Γ' := [at_ wn2 ⋎ ⊥ₗ]) (B := RA0)
          (mxSc1 (at_ wn2) (by simp)) (by simp) (by simp))))
    (.step (Γ' := [RA0, 𝐆 SA1, 𝐆 SA2, 𝐆 SA3, 𝐆 SA4, 𝐆 SA5, 𝐆 SA6, 𝐆 SA7, 𝐆 SA8, 𝐆 SA9, 𝐆 SA10,
        𝐆 TA1, 𝐆 TA2, 𝐆 TA3, 𝐆 TA4, 𝐆 TA5, 𝐆 TA6, 𝐆 TA7, 𝐆 TA8, 𝐆 TA9, 𝐆 TA10]) (B := mxInv)
      (.andR (A := RA0) (B := KA0) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 SA1) (B := KA1) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 SA2) (B := KA2) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 SA3) (B := KA3) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 SA4) (B := KA4) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 SA5) (B := KA5) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 SA6) (B := KA6) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 SA7) (B := KA7) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 SA8) (B := KA8) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 SA9) (B := KA9) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 SA10) (B := KA10) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 TA1) (B := KA11) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 TA2) (B := KA12) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 TA3) (B := KA13) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 TA4) (B := KA14) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 TA5) (B := KA15) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 TA6) (B := KA16) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 TA7) (B := KA17) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 TA8) (B := KA18) (by simp) (.close (by decide)) <|
       .andR (A := 𝐆 TA9) (B := KA19) (by simp) (.close (by decide)) <|
       .close (by decide))
      (by simp) (by simp))

theorem mxP3 : [mxInv] ⊢ [∼(ap crit1 ⋏ ap crit2)] :=
  .andL (A := RA0) (B := KA0) (by simp) <|
  .andL (A := 𝐆 SA1) (B := KA1) (by simp) <|
  .andL (A := 𝐆 SA2) (B := KA2) (by simp) <|
  .andL (A := 𝐆 SA3) (B := KA3) (by simp) <|
  .andL (A := 𝐆 SA4) (B := KA4) (by simp) <|
  .andL (A := 𝐆 SA5) (B := KA5) (by simp) <|
  .andL (A := 𝐆 SA6) (B := KA6) (by simp) <|
  .andL (A := 𝐆 SA7) (B := KA7) (by simp) <|
  .andL (A := 𝐆 SA8) (B := KA8) (by simp) <|
  .andL (A := 𝐆 SA9) (B := KA9) (by simp) <|
  .andL (A := 𝐆 SA10) (B := KA10) (by simp) <|
  .alwaysL (A := SA1) (by simp) <|
  .alwaysL (A := SA2) (by simp) <|
  .alwaysL (A := SA3) (by simp) <|
  .alwaysL (A := SA4) (by simp) <|
  .alwaysL (A := SA5) (by simp) <|
  .alwaysL (A := SA6) (by simp) <|
  .alwaysL (A := SA7) (by simp) <|
  .alwaysL (A := SA8) (by simp) <|
  .alwaysL (A := SA9) (by simp) <|
  .alwaysL (A := SA10) (by simp) <|
  .negR (A := ap crit1 ⋏ ap crit2) (by simp) <|
  .andL (A := ap crit1) (B := ap crit2) (by simp) <|
  .orL (A := at_ nn1) (B := RA1) (by simp)
    (.impL (A := at_ nn1) (B := ∼(ap crit1)) (by simp) (.close (by decide))
      (.negL (A := ap crit1) (by simp) (.close (by decide)))) <|
  .orL (A := at_ nn2) (B := RA2) (by simp)
    (.impL (A := at_ nn2) (B := ∼(ap crit1)) (by simp) (.close (by decide))
      (.negL (A := ap crit1) (by simp) (.close (by decide)))) <|
  .orL (A := at_ nw1) (B := RA3) (by simp)
    (.impL (A := at_ nw1) (B := ∼(ap crit1)) (by simp) (.close (by decide))
      (.negL (A := ap crit1) (by simp) (.close (by decide)))) <|
  .orL (A := at_ wn2) (B := RA4) (by simp)
    (.impL (A := at_ wn2) (B := ∼(ap crit1)) (by simp) (.close (by decide))
      (.negL (A := ap crit1) (by simp) (.close (by decide)))) <|
  .orL (A := at_ cn2) (B := RA5) (by simp)
    (.impL (A := at_ cn2) (B := ∼(ap crit2)) (by simp) (.close (by decide))
      (.negL (A := ap crit2) (by simp) (.close (by decide)))) <|
  .orL (A := at_ ww1) (B := RA6) (by simp)
    (.impL (A := at_ ww1) (B := ∼(ap crit1)) (by simp) (.close (by decide))
      (.negL (A := ap crit1) (by simp) (.close (by decide)))) <|
  .orL (A := at_ ww2) (B := RA7) (by simp)
    (.impL (A := at_ ww2) (B := ∼(ap crit1)) (by simp) (.close (by decide))
      (.negL (A := ap crit1) (by simp) (.close (by decide)))) <|
  .orL (A := at_ nc1) (B := RA8) (by simp)
    (.impL (A := at_ nc1) (B := ∼(ap crit1)) (by simp) (.close (by decide))
      (.negL (A := ap crit1) (by simp) (.close (by decide)))) <|
  .orL (A := at_ cw1) (B := at_ wc2) (by simp)
    (.impL (A := at_ cw1) (B := ∼(ap crit2)) (by simp) (.close (by decide))
      (.negL (A := ap crit2) (by simp) (.close (by decide))))
    (.impL (A := at_ wc2) (B := ∼(ap crit1)) (by simp) (.close (by decide))
      (.negL (A := ap crit1) (by simp) (.close (by decide))))

theorem candidate : S.hyps ⊢ [lift specMutex] := by
  show [(at_ nn1 ⋎ (at_ nn2 ⋎ ⊥ₗ)), 𝐆 (at_ nn1 ⇒ ∼(ap crit1)), 𝐆 (at_ nn1 ⇒ ∼(ap crit2)), 𝐆 (at_ nn1 ⇒ 𝐗 (at_ wn2 ⋎ (at_ nw1 ⋎ ⊥ₗ))), 𝐆 (at_ nn2 ⇒ ∼(ap crit1)), 𝐆 (at_ nn2 ⇒ ∼(ap crit2)), 𝐆 (at_ nn2 ⇒ 𝐗 (at_ wn2 ⋎ (at_ nw1 ⋎ ⊥ₗ))), 𝐆 (at_ nw1 ⇒ ∼(ap crit1)), 𝐆 (at_ nw1 ⇒ ∼(ap crit2)), 𝐆 (at_ nw1 ⇒ 𝐗 (at_ ww2 ⋎ (at_ nc1 ⋎ ⊥ₗ))), 𝐆 (at_ nw2 ⇒ ∼(ap crit1)), 𝐆 (at_ nw2 ⇒ ∼(ap crit2)), 𝐆 (at_ nw2 ⇒ 𝐗 (at_ ww2 ⋎ (at_ nc2 ⋎ ⊥ₗ))), 𝐆 (at_ nc1 ⇒ ap crit2), 𝐆 (at_ nc1 ⇒ ∼(ap crit1)), 𝐆 (at_ nc1 ⇒ 𝐗 (at_ wc2 ⋎ (at_ nn1 ⋎ ⊥ₗ))), 𝐆 (at_ nc2 ⇒ ap crit2), 𝐆 (at_ nc2 ⇒ ∼(ap crit1)), 𝐆 (at_ nc2 ⇒ 𝐗 (at_ wc2 ⋎ (at_ nn2 ⋎ ⊥ₗ))), 𝐆 (at_ wn1 ⇒ ∼(ap crit1)), 𝐆 (at_ wn1 ⇒ ∼(ap crit2)), 𝐆 (at_ wn1 ⇒ 𝐗 (at_ cn1 ⋎ (at_ ww1 ⋎ ⊥ₗ))), 𝐆 (at_ wn2 ⇒ ∼(ap crit1)), 𝐆 (at_ wn2 ⇒ ∼(ap crit2)), 𝐆 (at_ wn2 ⇒ 𝐗 (at_ cn2 ⋎ (at_ ww1 ⋎ ⊥ₗ))), 𝐆 (at_ ww1 ⇒ ∼(ap crit1)), 𝐆 (at_ ww1 ⇒ ∼(ap crit2)), 𝐆 (at_ ww1 ⇒ 𝐗 (at_ cw1 ⋎ ⊥ₗ)), 𝐆 (at_ ww2 ⇒ ∼(ap crit1)), 𝐆 (at_ ww2 ⇒ ∼(ap crit2)), 𝐆 (at_ ww2 ⇒ 𝐗 (at_ wc2 ⋎ ⊥ₗ)), 𝐆 (at_ wc1 ⇒ ap crit2), 𝐆 (at_ wc1 ⇒ ∼(ap crit1)), 𝐆 (at_ wc1 ⇒ 𝐗 (at_ cc1 ⋎ (at_ wn1 ⋎ ⊥ₗ))), 𝐆 (at_ wc2 ⇒ ap crit2), 𝐆 (at_ wc2 ⇒ ∼(ap crit1)), 𝐆 (at_ wc2 ⇒ 𝐗 (at_ wn2 ⋎ ⊥ₗ)), 𝐆 (at_ cn1 ⇒ ap crit1), 𝐆 (at_ cn1 ⇒ ∼(ap crit2)), 𝐆 (at_ cn1 ⇒ 𝐗 (at_ nn1 ⋎ (at_ cw1 ⋎ ⊥ₗ))), 𝐆 (at_ cn2 ⇒ ap crit1), 𝐆 (at_ cn2 ⇒ ∼(ap crit2)), 𝐆 (at_ cn2 ⇒ 𝐗 (at_ nn2 ⋎ (at_ cw1 ⋎ ⊥ₗ))), 𝐆 (at_ cw1 ⇒ ap crit1), 𝐆 (at_ cw1 ⇒ ∼(ap crit2)), 𝐆 (at_ cw1 ⇒ 𝐗 (at_ nw1 ⋎ ⊥ₗ)), 𝐆 (at_ cw2 ⇒ ap crit1), 𝐆 (at_ cw2 ⇒ ∼(ap crit2)), 𝐆 (at_ cw2 ⇒ 𝐗 (at_ nw2 ⋎ (at_ cc2 ⋎ ⊥ₗ))), 𝐆 (at_ cc1 ⇒ ap crit1), 𝐆 (at_ cc1 ⇒ ap crit2), 𝐆 (at_ cc1 ⇒ 𝐗 (at_ nc1 ⋎ (at_ cn1 ⋎ ⊥ₗ))), 𝐆 (at_ cc2 ⇒ ap crit1), 𝐆 (at_ cc2 ⇒ ap crit2), 𝐆 (at_ cc2 ⇒ 𝐗 (at_ nc2 ⋎ (at_ cn2 ⋎ ⊥ₗ)))] ⊢ [𝐆 (∼(ap crit1 ⋏ ap crit2))]
  exact .alwaysR (I := mxInv) (A := ∼(ap crit1 ⋏ ap crit2)) (by simp)
    (.wk mxP1 (by simp) (by simp)) mxP2 mxP3

end Candidate

theorem verified : Bench.Peterson.S.Models Bench.Peterson.specMutex :=
  Bench.Peterson.S.sat_of_derives Candidate.candidate

#print axioms verified
