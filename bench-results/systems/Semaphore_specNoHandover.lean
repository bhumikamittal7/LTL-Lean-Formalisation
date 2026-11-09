import Bench

open LTL LTL.System
open Bench.Semaphore
open Bench.Semaphore.P Bench.Semaphore.St

namespace Candidate

abbrev Loc7 : Formula (P ⊕ St) := at_ cw0 ⋎ at_ wc0
abbrev Loc6 : Formula (P ⊕ St) := at_ nc0 ⋎ Loc7
abbrev Loc5 : Formula (P ⊕ St) := at_ ww1 ⋎ Loc6
abbrev Loc4 : Formula (P ⊕ St) := at_ cn0 ⋎ Loc5
abbrev Loc3 : Formula (P ⊕ St) := at_ nw1 ⋎ Loc4
abbrev Loc2 : Formula (P ⊕ St) := at_ wn1 ⋎ Loc3
abbrev Loc : Formula (P ⊕ St) := at_ nn1 ⋎ Loc2

abbrev tr1 : Formula (P ⊕ St) := at_ nn1 ⇒ 𝐗 (at_ wn1 ⋎ (at_ nw1 ⋎ ⊥ₗ))
abbrev tr2 : Formula (P ⊕ St) := at_ wn1 ⇒ 𝐗 (at_ cn0 ⋎ (at_ ww1 ⋎ ⊥ₗ))
abbrev tr3 : Formula (P ⊕ St) := at_ nw1 ⇒ 𝐗 (at_ ww1 ⋎ (at_ nc0 ⋎ ⊥ₗ))
abbrev tr4 : Formula (P ⊕ St) := at_ cn0 ⇒ 𝐗 (at_ nn1 ⋎ (at_ cw0 ⋎ ⊥ₗ))
abbrev tr5 : Formula (P ⊕ St) := at_ ww1 ⇒ 𝐗 (at_ cw0 ⋎ (at_ wc0 ⋎ ⊥ₗ))
abbrev tr6 : Formula (P ⊕ St) := at_ nc0 ⇒ 𝐗 (at_ wc0 ⋎ (at_ nn1 ⋎ ⊥ₗ))
abbrev tr7 : Formula (P ⊕ St) := at_ cw0 ⇒ 𝐗 (at_ nw1 ⋎ ⊥ₗ)
abbrev tr8 : Formula (P ⊕ St) := at_ wc0 ⇒ 𝐗 (at_ wn1 ⋎ ⊥ₗ)
abbrev na1 : Formula (P ⊕ St) := at_ nn1 ⇒ ∼(ap crit1)
abbrev na2 : Formula (P ⊕ St) := at_ wn1 ⇒ ∼(ap crit1)
abbrev na3 : Formula (P ⊕ St) := at_ nw1 ⇒ ∼(ap crit1)
abbrev na5 : Formula (P ⊕ St) := at_ ww1 ⇒ ∼(ap crit1)
abbrev na6 : Formula (P ⊕ St) := at_ nc0 ⇒ ∼(ap crit1)
abbrev na8 : Formula (P ⊕ St) := at_ wc0 ⇒ ∼(ap crit1)
abbrev nb1 : Formula (P ⊕ St) := at_ nn1 ⇒ ∼(ap crit2)
abbrev nb3 : Formula (P ⊕ St) := at_ nw1 ⇒ ∼(ap crit2)
abbrev nb7 : Formula (P ⊕ St) := at_ cw0 ⇒ ∼(ap crit2)

abbrev Cc16 : Formula (P ⊕ St) := (𝐆 nb3) ⋏ (𝐆 nb7)
abbrev Cc15 : Formula (P ⊕ St) := (𝐆 nb1) ⋏ Cc16
abbrev Cc14 : Formula (P ⊕ St) := (𝐆 na8) ⋏ Cc15
abbrev Cc13 : Formula (P ⊕ St) := (𝐆 na6) ⋏ Cc14
abbrev Cc12 : Formula (P ⊕ St) := (𝐆 na5) ⋏ Cc13
abbrev Cc11 : Formula (P ⊕ St) := (𝐆 na3) ⋏ Cc12
abbrev Cc10 : Formula (P ⊕ St) := (𝐆 na2) ⋏ Cc11
abbrev Cc9 : Formula (P ⊕ St) := (𝐆 na1) ⋏ Cc10
abbrev Cc8 : Formula (P ⊕ St) := (𝐆 tr8) ⋏ Cc9
abbrev Cc7 : Formula (P ⊕ St) := (𝐆 tr7) ⋏ Cc8
abbrev Cc6 : Formula (P ⊕ St) := (𝐆 tr6) ⋏ Cc7
abbrev Cc5 : Formula (P ⊕ St) := (𝐆 tr5) ⋏ Cc6
abbrev Cc4 : Formula (P ⊕ St) := (𝐆 tr4) ⋏ Cc5
abbrev Cc3 : Formula (P ⊕ St) := (𝐆 tr3) ⋏ Cc4
abbrev Cc2 : Formula (P ⊕ St) := (𝐆 tr2) ⋏ Cc3
abbrev Gall : Formula (P ⊕ St) := (𝐆 tr1) ⋏ Cc2
abbrev Invt : Formula (P ⊕ St) := Loc ⋏ Gall

theorem loc_R {Γ Δ : List (Formula (P ⊕ St))}
    (h : Γ ⊢ [at_ nn1, at_ wn1, at_ nw1, at_ cn0, at_ ww1, at_ nc0, at_ cw0, at_ wc0]) :
    Γ ⊢ Loc :: Δ :=
  .orR (A := at_ nn1) (B := Loc2) (by simp) <|
  .orR (A := at_ wn1) (B := Loc3) (by simp) <|
  .orR (A := at_ nw1) (B := Loc4) (by simp) <|
  .orR (A := at_ cn0) (B := Loc5) (by simp) <|
  .orR (A := at_ ww1) (B := Loc6) (by simp) <|
  .orR (A := at_ nc0) (B := Loc7) (by simp) <|
  .orR (A := at_ cw0) (B := at_ wc0) (by simp) <|
  .wk h (fun x hx => hx) (by simp)

theorem gall_R : [𝐆 tr1, 𝐆 tr2, 𝐆 tr3, 𝐆 tr4, 𝐆 tr5, 𝐆 tr6, 𝐆 tr7, 𝐆 tr8,
    𝐆 na1, 𝐆 na2, 𝐆 na3, 𝐆 na5, 𝐆 na6, 𝐆 na8, 𝐆 nb1, 𝐆 nb3, 𝐆 nb7] ⊢ [Gall] :=
  .andR (A := 𝐆 tr1) (B := Cc2) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 tr2) (B := Cc3) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 tr3) (B := Cc4) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 tr4) (B := Cc5) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 tr5) (B := Cc6) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 tr6) (B := Cc7) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 tr7) (B := Cc8) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 tr8) (B := Cc9) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 na1) (B := Cc10) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 na2) (B := Cc11) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 na3) (B := Cc12) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 na5) (B := Cc13) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 na6) (B := Cc14) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 na8) (B := Cc15) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 nb1) (B := Cc16) (by simp) (.close (by decide)) <|
  .andR (A := 𝐆 nb3) (B := 𝐆 nb7) (by simp) (.close (by decide)) (.close (by decide))

theorem inv_unpack {Δ : List (Formula (P ⊕ St))}
    (h : [Loc, 𝐆 tr1, 𝐆 tr2, 𝐆 tr3, 𝐆 tr4, 𝐆 tr5, 𝐆 tr6, 𝐆 tr7, 𝐆 tr8,
      𝐆 na1, 𝐆 na2, 𝐆 na3, 𝐆 na5, 𝐆 na6, 𝐆 na8, 𝐆 nb1, 𝐆 nb3, 𝐆 nb7] ⊢ Δ) :
    [Invt] ⊢ Δ :=
  .andL (A := Loc) (B := Gall) (by simp) <|
  .andL (A := 𝐆 tr1) (B := Cc2) (by simp) <|
  .andL (A := 𝐆 tr2) (B := Cc3) (by simp) <|
  .andL (A := 𝐆 tr3) (B := Cc4) (by simp) <|
  .andL (A := 𝐆 tr4) (B := Cc5) (by simp) <|
  .andL (A := 𝐆 tr5) (B := Cc6) (by simp) <|
  .andL (A := 𝐆 tr6) (B := Cc7) (by simp) <|
  .andL (A := 𝐆 tr7) (B := Cc8) (by simp) <|
  .andL (A := 𝐆 tr8) (B := Cc9) (by simp) <|
  .andL (A := 𝐆 na1) (B := Cc10) (by simp) <|
  .andL (A := 𝐆 na2) (B := Cc11) (by simp) <|
  .andL (A := 𝐆 na3) (B := Cc12) (by simp) <|
  .andL (A := 𝐆 na5) (B := Cc13) (by simp) <|
  .andL (A := 𝐆 na6) (B := Cc14) (by simp) <|
  .andL (A := 𝐆 na8) (B := Cc15) (by simp) <|
  .andL (A := 𝐆 nb1) (B := Cc16) (by simp) <|
  .andL (A := 𝐆 nb3) (B := 𝐆 nb7) (by simp) <|
  .wk h (by simp) (fun x hx => hx)

theorem nx2 {a b : Formula (P ⊕ St)}
    (ha : a ∈ [at_ nn1, at_ wn1, at_ nw1, at_ cn0, at_ ww1, at_ nc0, at_ cw0, at_ wc0])
    (hb : b ∈ [at_ nn1, at_ wn1, at_ nw1, at_ cn0, at_ ww1, at_ nc0, at_ cw0, at_ wc0]) :
    [a ⋎ (b ⋎ ⊥ₗ), Gall] ⊢ [Invt] :=
  .andR (A := Loc) (B := Gall) (by simp)
    (loc_R (.orL (A := a) (B := b ⋎ ⊥ₗ) (by simp)
      (.ax (A := a) (by simp) ha)
      (.orL (A := b) (B := ⊥ₗ) (by simp)
        (.ax (A := b) (by simp) hb)
        (.botL (by simp)))))
    (.ax (A := Gall) (by simp) (by simp))

theorem nx1 {a : Formula (P ⊕ St)}
    (ha : a ∈ [at_ nn1, at_ wn1, at_ nw1, at_ cn0, at_ ww1, at_ nc0, at_ cw0, at_ wc0]) :
    [a ⋎ ⊥ₗ, Gall] ⊢ [Invt] :=
  .andR (A := Loc) (B := Gall) (by simp)
    (loc_R (.orL (A := a) (B := ⊥ₗ) (by simp)
      (.ax (A := a) (by simp) ha)
      (.botL (by simp))))
    (.ax (A := Gall) (by simp) (by simp))

theorem presv : [Invt] ⊢ [𝐗 Invt] :=
  inv_unpack <|
  .alwaysL (A := tr1) (by simp) <|
  .alwaysL (A := tr2) (by simp) <|
  .alwaysL (A := tr3) (by simp) <|
  .alwaysL (A := tr4) (by simp) <|
  .alwaysL (A := tr5) (by simp) <|
  .alwaysL (A := tr6) (by simp) <|
  .alwaysL (A := tr7) (by simp) <|
  .alwaysL (A := tr8) (by simp) <|
  .alwaysL (A := na1) (by simp) <|
  .alwaysL (A := na2) (by simp) <|
  .alwaysL (A := na3) (by simp) <|
  .alwaysL (A := na5) (by simp) <|
  .alwaysL (A := na6) (by simp) <|
  .alwaysL (A := na8) (by simp) <|
  .alwaysL (A := nb1) (by simp) <|
  .alwaysL (A := nb3) (by simp) <|
  .alwaysL (A := nb7) (by simp) <|
  .cut (𝐗 Gall)
    (.step (Γ' := [𝐆 tr1, 𝐆 tr2, 𝐆 tr3, 𝐆 tr4, 𝐆 tr5, 𝐆 tr6, 𝐆 tr7, 𝐆 tr8,
        𝐆 na1, 𝐆 na2, 𝐆 na3, 𝐆 na5, 𝐆 na6, 𝐆 na8, 𝐆 nb1, 𝐆 nb3, 𝐆 nb7])
      (B := Gall) gall_R (by simp) (by simp)) <|
  .orL (A := at_ nn1) (B := Loc2) (by simp)
    (.impL (A := at_ nn1) (B := 𝐗 (at_ wn1 ⋎ (at_ nw1 ⋎ ⊥ₗ))) (by simp) (.close (by decide)) <|
      .step (Γ' := [at_ wn1 ⋎ (at_ nw1 ⋎ ⊥ₗ), Gall]) (B := Invt)
        (nx2 (by simp) (by simp)) (by simp) (by simp)) <|
  .orL (A := at_ wn1) (B := Loc3) (by simp)
    (.impL (A := at_ wn1) (B := 𝐗 (at_ cn0 ⋎ (at_ ww1 ⋎ ⊥ₗ))) (by simp) (.close (by decide)) <|
      .step (Γ' := [at_ cn0 ⋎ (at_ ww1 ⋎ ⊥ₗ), Gall]) (B := Invt)
        (nx2 (by simp) (by simp)) (by simp) (by simp)) <|
  .orL (A := at_ nw1) (B := Loc4) (by simp)
    (.impL (A := at_ nw1) (B := 𝐗 (at_ ww1 ⋎ (at_ nc0 ⋎ ⊥ₗ))) (by simp) (.close (by decide)) <|
      .step (Γ' := [at_ ww1 ⋎ (at_ nc0 ⋎ ⊥ₗ), Gall]) (B := Invt)
        (nx2 (by simp) (by simp)) (by simp) (by simp)) <|
  .orL (A := at_ cn0) (B := Loc5) (by simp)
    (.impL (A := at_ cn0) (B := 𝐗 (at_ nn1 ⋎ (at_ cw0 ⋎ ⊥ₗ))) (by simp) (.close (by decide)) <|
      .step (Γ' := [at_ nn1 ⋎ (at_ cw0 ⋎ ⊥ₗ), Gall]) (B := Invt)
        (nx2 (by simp) (by simp)) (by simp) (by simp)) <|
  .orL (A := at_ ww1) (B := Loc6) (by simp)
    (.impL (A := at_ ww1) (B := 𝐗 (at_ cw0 ⋎ (at_ wc0 ⋎ ⊥ₗ))) (by simp) (.close (by decide)) <|
      .step (Γ' := [at_ cw0 ⋎ (at_ wc0 ⋎ ⊥ₗ), Gall]) (B := Invt)
        (nx2 (by simp) (by simp)) (by simp) (by simp)) <|
  .orL (A := at_ nc0) (B := Loc7) (by simp)
    (.impL (A := at_ nc0) (B := 𝐗 (at_ wc0 ⋎ (at_ nn1 ⋎ ⊥ₗ))) (by simp) (.close (by decide)) <|
      .step (Γ' := [at_ wc0 ⋎ (at_ nn1 ⋎ ⊥ₗ), Gall]) (B := Invt)
        (nx2 (by simp) (by simp)) (by simp) (by simp)) <|
  .orL (A := at_ cw0) (B := at_ wc0) (by simp)
    (.impL (A := at_ cw0) (B := 𝐗 (at_ nw1 ⋎ ⊥ₗ)) (by simp) (.close (by decide)) <|
      .step (Γ' := [at_ nw1 ⋎ ⊥ₗ, Gall]) (B := Invt)
        (nx1 (by simp)) (by simp) (by simp))
    (.impL (A := at_ wc0) (B := 𝐗 (at_ wn1 ⋎ ⊥ₗ)) (by simp) (.close (by decide)) <|
      .step (Γ' := [at_ wn1 ⋎ ⊥ₗ, Gall]) (B := Invt)
        (nx1 (by simp)) (by simp) (by simp))

theorem cn0Next : [at_ nn1 ⋎ (at_ cw0 ⋎ ⊥ₗ), 𝐆 nb1, 𝐆 nb7] ⊢ [∼(ap crit2)] :=
  .negR (A := ap crit2) (by simp) <|
  .orL (A := at_ nn1) (B := at_ cw0 ⋎ ⊥ₗ) (by simp)
    (.alwaysL (A := nb1) (by simp) <|
      .impL (A := at_ nn1) (B := ∼(ap crit2)) (by simp) (.close (by decide)) <|
      .negL (A := ap crit2) (by simp) (.close (by decide)))
    (.orL (A := at_ cw0) (B := ⊥ₗ) (by simp)
      (.alwaysL (A := nb7) (by simp) <|
        .impL (A := at_ cw0) (B := ∼(ap crit2)) (by simp) (.close (by decide)) <|
        .negL (A := ap crit2) (by simp) (.close (by decide)))
      (.botL (by simp)))

theorem cw0Next : [at_ nw1 ⋎ ⊥ₗ, 𝐆 nb3] ⊢ [∼(ap crit2)] :=
  .negR (A := ap crit2) (by simp) <|
  .orL (A := at_ nw1) (B := ⊥ₗ) (by simp)
    (.alwaysL (A := nb3) (by simp) <|
      .impL (A := at_ nw1) (B := ∼(ap crit2)) (by simp) (.close (by decide)) <|
      .negL (A := ap crit2) (by simp) (.close (by decide)))
    (.botL (by simp))

theorem goalPf : [Invt] ⊢ [ap crit1 ⇒ 𝐗 (∼(ap crit2))] :=
  inv_unpack <|
  .impR (A := ap crit1) (B := 𝐗 (∼(ap crit2))) (by simp) <|
  .orL (A := at_ nn1) (B := Loc2) (by simp)
    (.alwaysL (A := na1) (by simp) <|
      .impL (A := at_ nn1) (B := ∼(ap crit1)) (by simp) (.close (by decide)) <|
      .negL (A := ap crit1) (by simp) (.close (by decide))) <|
  .orL (A := at_ wn1) (B := Loc3) (by simp)
    (.alwaysL (A := na2) (by simp) <|
      .impL (A := at_ wn1) (B := ∼(ap crit1)) (by simp) (.close (by decide)) <|
      .negL (A := ap crit1) (by simp) (.close (by decide))) <|
  .orL (A := at_ nw1) (B := Loc4) (by simp)
    (.alwaysL (A := na3) (by simp) <|
      .impL (A := at_ nw1) (B := ∼(ap crit1)) (by simp) (.close (by decide)) <|
      .negL (A := ap crit1) (by simp) (.close (by decide))) <|
  .orL (A := at_ cn0) (B := Loc5) (by simp)
    (.alwaysL (A := tr4) (by simp) <|
      .impL (A := at_ cn0) (B := 𝐗 (at_ nn1 ⋎ (at_ cw0 ⋎ ⊥ₗ))) (by simp) (.close (by decide)) <|
      .alwaysL (A := nb1) (by simp) <|
      .alwaysL (A := nb7) (by simp) <|
      .step (Γ' := [at_ nn1 ⋎ (at_ cw0 ⋎ ⊥ₗ), 𝐆 nb1, 𝐆 nb7]) (B := ∼(ap crit2))
        cn0Next (by simp) (by simp)) <|
  .orL (A := at_ ww1) (B := Loc6) (by simp)
    (.alwaysL (A := na5) (by simp) <|
      .impL (A := at_ ww1) (B := ∼(ap crit1)) (by simp) (.close (by decide)) <|
      .negL (A := ap crit1) (by simp) (.close (by decide))) <|
  .orL (A := at_ nc0) (B := Loc7) (by simp)
    (.alwaysL (A := na6) (by simp) <|
      .impL (A := at_ nc0) (B := ∼(ap crit1)) (by simp) (.close (by decide)) <|
      .negL (A := ap crit1) (by simp) (.close (by decide))) <|
  .orL (A := at_ cw0) (B := at_ wc0) (by simp)
    (.alwaysL (A := tr7) (by simp) <|
      .impL (A := at_ cw0) (B := 𝐗 (at_ nw1 ⋎ ⊥ₗ)) (by simp) (.close (by decide)) <|
      .alwaysL (A := nb3) (by simp) <|
      .step (Γ' := [at_ nw1 ⋎ ⊥ₗ, 𝐆 nb3]) (B := ∼(ap crit2))
        cw0Next (by simp) (by simp))
    (.alwaysL (A := na8) (by simp) <|
      .impL (A := at_ wc0) (B := ∼(ap crit1)) (by simp) (.close (by decide)) <|
      .negL (A := ap crit1) (by simp) (.close (by decide)))

theorem candidate : S.hyps ⊢ [lift specNoHandover] := by
  show [(at_ nn1 ⋎ ⊥ₗ), 𝐆 (at_ nn0 ⇒ ∼(ap crit1)), 𝐆 (at_ nn0 ⇒ ∼(ap crit2)), 𝐆 (at_ nn0 ⇒ 𝐗 (at_ wn0 ⋎ (at_ nw0 ⋎ ⊥ₗ))), 𝐆 (at_ nn1 ⇒ ∼(ap crit1)), 𝐆 (at_ nn1 ⇒ ∼(ap crit2)), 𝐆 (at_ nn1 ⇒ 𝐗 (at_ wn1 ⋎ (at_ nw1 ⋎ ⊥ₗ))), 𝐆 (at_ nw0 ⇒ ∼(ap crit1)), 𝐆 (at_ nw0 ⇒ ∼(ap crit2)), 𝐆 (at_ nw0 ⇒ 𝐗 (at_ ww0 ⋎ ⊥ₗ)), 𝐆 (at_ nw1 ⇒ ∼(ap crit1)), 𝐆 (at_ nw1 ⇒ ∼(ap crit2)), 𝐆 (at_ nw1 ⇒ 𝐗 (at_ ww1 ⋎ (at_ nc0 ⋎ ⊥ₗ))), 𝐆 (at_ nc0 ⇒ ap crit2), 𝐆 (at_ nc0 ⇒ ∼(ap crit1)), 𝐆 (at_ nc0 ⇒ 𝐗 (at_ wc0 ⋎ (at_ nn1 ⋎ ⊥ₗ))), 𝐆 (at_ nc1 ⇒ ap crit2), 𝐆 (at_ nc1 ⇒ ∼(ap crit1)), 𝐆 (at_ nc1 ⇒ 𝐗 (at_ wc1 ⋎ (at_ nn1 ⋎ ⊥ₗ))), 𝐆 (at_ wn0 ⇒ ∼(ap crit1)), 𝐆 (at_ wn0 ⇒ ∼(ap crit2)), 𝐆 (at_ wn0 ⇒ 𝐗 (at_ ww0 ⋎ ⊥ₗ)), 𝐆 (at_ wn1 ⇒ ∼(ap crit1)), 𝐆 (at_ wn1 ⇒ ∼(ap crit2)), 𝐆 (at_ wn1 ⇒ 𝐗 (at_ cn0 ⋎ (at_ ww1 ⋎ ⊥ₗ))), 𝐆 (at_ ww0 ⇒ ∼(ap crit1)), 𝐆 (at_ ww0 ⇒ ∼(ap crit2)), 𝐆 (at_ ww0 ⇒ 𝐗 (at_ ww0 ⋎ ⊥ₗ)), 𝐆 (at_ ww1 ⇒ ∼(ap crit1)), 𝐆 (at_ ww1 ⇒ ∼(ap crit2)), 𝐆 (at_ ww1 ⇒ 𝐗 (at_ cw0 ⋎ (at_ wc0 ⋎ ⊥ₗ))), 𝐆 (at_ wc0 ⇒ ap crit2), 𝐆 (at_ wc0 ⇒ ∼(ap crit1)), 𝐆 (at_ wc0 ⇒ 𝐗 (at_ wn1 ⋎ ⊥ₗ)), 𝐆 (at_ wc1 ⇒ ap crit2), 𝐆 (at_ wc1 ⇒ ∼(ap crit1)), 𝐆 (at_ wc1 ⇒ 𝐗 (at_ cc0 ⋎ (at_ wn1 ⋎ ⊥ₗ))), 𝐆 (at_ cn0 ⇒ ap crit1), 𝐆 (at_ cn0 ⇒ ∼(ap crit2)), 𝐆 (at_ cn0 ⇒ 𝐗 (at_ nn1 ⋎ (at_ cw0 ⋎ ⊥ₗ))), 𝐆 (at_ cn1 ⇒ ap crit1), 𝐆 (at_ cn1 ⇒ ∼(ap crit2)), 𝐆 (at_ cn1 ⇒ 𝐗 (at_ nn1 ⋎ (at_ cw1 ⋎ ⊥ₗ))), 𝐆 (at_ cw0 ⇒ ap crit1), 𝐆 (at_ cw0 ⇒ ∼(ap crit2)), 𝐆 (at_ cw0 ⇒ 𝐗 (at_ nw1 ⋎ ⊥ₗ)), 𝐆 (at_ cw1 ⇒ ap crit1), 𝐆 (at_ cw1 ⇒ ∼(ap crit2)), 𝐆 (at_ cw1 ⇒ 𝐗 (at_ nw1 ⋎ (at_ cc0 ⋎ ⊥ₗ))), 𝐆 (at_ cc0 ⇒ ap crit1), 𝐆 (at_ cc0 ⇒ ap crit2), 𝐆 (at_ cc0 ⇒ 𝐗 (at_ nc1 ⋎ (at_ cn1 ⋎ ⊥ₗ))), 𝐆 (at_ cc1 ⇒ ap crit1), 𝐆 (at_ cc1 ⇒ ap crit2), 𝐆 (at_ cc1 ⇒ 𝐗 (at_ nc1 ⋎ (at_ cn1 ⋎ ⊥ₗ)))] ⊢ [𝐆 (ap crit1 ⇒ 𝐗 (∼(ap crit2)))]
  exact .alwaysR (A := ap crit1 ⇒ 𝐗 (∼(ap crit2))) Invt (by simp)
    (.andR (A := Loc) (B := Gall) (by simp)
      (.orL (A := at_ nn1) (B := ⊥ₗ) (by simp)
        (.orR (A := at_ nn1) (B := Loc2) (by simp) (.close (by decide)))
        (.botL (by simp)))
      (.wk gall_R (by simp) (by simp)))
    presv goalPf

end Candidate

theorem verified : Bench.Semaphore.S.Models Bench.Semaphore.specNoHandover :=
  Bench.Semaphore.S.sat_of_derives Candidate.candidate

#print axioms verified
