import Bench

open LTL LTL.System
open Bench.Semaphore
open Bench.Semaphore.P Bench.Semaphore.St

namespace Candidate

abbrev D7 : Formula (P ⊕ St) := at_ wc0 ⋎ ⊥ₗ
abbrev D6 : Formula (P ⊕ St) := at_ cw0 ⋎ D7
abbrev D5 : Formula (P ⊕ St) := at_ nc0 ⋎ D6
abbrev D4 : Formula (P ⊕ St) := at_ ww1 ⋎ D5
abbrev D3 : Formula (P ⊕ St) := at_ cn0 ⋎ D4
abbrev D2 : Formula (P ⊕ St) := at_ nw1 ⋎ D3
abbrev D1 : Formula (P ⊕ St) := at_ wn1 ⋎ D2
abbrev D0 : Formula (P ⊕ St) := at_ nn1 ⋎ D1

abbrev N_nn1 : Formula (P ⊕ St) := at_ wn1 ⋎ (at_ nw1 ⋎ ⊥ₗ)
abbrev N_wn1 : Formula (P ⊕ St) := at_ cn0 ⋎ (at_ ww1 ⋎ ⊥ₗ)
abbrev N_nw1 : Formula (P ⊕ St) := at_ ww1 ⋎ (at_ nc0 ⋎ ⊥ₗ)
abbrev N_cn0 : Formula (P ⊕ St) := at_ nn1 ⋎ (at_ cw0 ⋎ ⊥ₗ)
abbrev N_ww1 : Formula (P ⊕ St) := at_ cw0 ⋎ (at_ wc0 ⋎ ⊥ₗ)
abbrev N_nc0 : Formula (P ⊕ St) := at_ wc0 ⋎ (at_ nn1 ⋎ ⊥ₗ)
abbrev N_cw0 : Formula (P ⊕ St) := at_ nw1 ⋎ ⊥ₗ
abbrev N_wc0 : Formula (P ⊕ St) := at_ wn1 ⋎ ⊥ₗ

abbrev Tr_nn1 : Formula (P ⊕ St) := 𝐆 (at_ nn1 ⇒ 𝐗 N_nn1)
abbrev Tr_wn1 : Formula (P ⊕ St) := 𝐆 (at_ wn1 ⇒ 𝐗 N_wn1)
abbrev Tr_nw1 : Formula (P ⊕ St) := 𝐆 (at_ nw1 ⇒ 𝐗 N_nw1)
abbrev Tr_cn0 : Formula (P ⊕ St) := 𝐆 (at_ cn0 ⇒ 𝐗 N_cn0)
abbrev Tr_ww1 : Formula (P ⊕ St) := 𝐆 (at_ ww1 ⇒ 𝐗 N_ww1)
abbrev Tr_nc0 : Formula (P ⊕ St) := 𝐆 (at_ nc0 ⇒ 𝐗 N_nc0)
abbrev Tr_cw0 : Formula (P ⊕ St) := 𝐆 (at_ cw0 ⇒ 𝐗 N_cw0)
abbrev Tr_wc0 : Formula (P ⊕ St) := 𝐆 (at_ wc0 ⇒ 𝐗 N_wc0)

abbrev Sf_nn1 : Formula (P ⊕ St) := 𝐆 (at_ nn1 ⇒ ∼(ap crit1))
abbrev Sf_wn1 : Formula (P ⊕ St) := 𝐆 (at_ wn1 ⇒ ∼(ap crit1))
abbrev Sf_nw1 : Formula (P ⊕ St) := 𝐆 (at_ nw1 ⇒ ∼(ap crit1))
abbrev Sf_cn0 : Formula (P ⊕ St) := 𝐆 (at_ cn0 ⇒ ∼(ap crit2))
abbrev Sf_ww1 : Formula (P ⊕ St) := 𝐆 (at_ ww1 ⇒ ∼(ap crit1))
abbrev Sf_nc0 : Formula (P ⊕ St) := 𝐆 (at_ nc0 ⇒ ∼(ap crit1))
abbrev Sf_cw0 : Formula (P ⊕ St) := 𝐆 (at_ cw0 ⇒ ∼(ap crit2))
abbrev Sf_wc0 : Formula (P ⊕ St) := 𝐆 (at_ wc0 ⇒ ∼(ap crit1))

abbrev F15 : Formula (P ⊕ St) := Sf_cw0 ⋏ Sf_wc0
abbrev F14 : Formula (P ⊕ St) := Sf_nc0 ⋏ F15
abbrev F13 : Formula (P ⊕ St) := Sf_ww1 ⋏ F14
abbrev F12 : Formula (P ⊕ St) := Sf_cn0 ⋏ F13
abbrev F11 : Formula (P ⊕ St) := Sf_nw1 ⋏ F12
abbrev F10 : Formula (P ⊕ St) := Sf_wn1 ⋏ F11
abbrev F9 : Formula (P ⊕ St) := Sf_nn1 ⋏ F10
abbrev F8 : Formula (P ⊕ St) := Tr_wc0 ⋏ F9
abbrev F7 : Formula (P ⊕ St) := Tr_cw0 ⋏ F8
abbrev F6 : Formula (P ⊕ St) := Tr_nc0 ⋏ F7
abbrev F5 : Formula (P ⊕ St) := Tr_ww1 ⋏ F6
abbrev F4 : Formula (P ⊕ St) := Tr_cn0 ⋏ F5
abbrev F3 : Formula (P ⊕ St) := Tr_nw1 ⋏ F4
abbrev F2 : Formula (P ⊕ St) := Tr_wn1 ⋏ F3
abbrev F1 : Formula (P ⊕ St) := Tr_nn1 ⋏ F2

abbrev Inv : Formula (P ⊕ St) := D0 ⋏ F1

set_option maxHeartbeats 4000000 in
theorem sm_lF : [Tr_nn1, Tr_wn1, Tr_nw1, Tr_cn0, Tr_ww1, Tr_nc0, Tr_cw0, Tr_wc0, Sf_nn1, Sf_wn1, Sf_nw1, Sf_cn0, Sf_ww1, Sf_nc0, Sf_cw0, Sf_wc0] ⊢ [F1] :=
  .andR (A := Tr_nn1) (B := F2) (by simp) (.ax (A := Tr_nn1) (by simp) (by simp)) <|
  .andR (A := Tr_wn1) (B := F3) (by simp) (.ax (A := Tr_wn1) (by simp) (by simp)) <|
  .andR (A := Tr_nw1) (B := F4) (by simp) (.ax (A := Tr_nw1) (by simp) (by simp)) <|
  .andR (A := Tr_cn0) (B := F5) (by simp) (.ax (A := Tr_cn0) (by simp) (by simp)) <|
  .andR (A := Tr_ww1) (B := F6) (by simp) (.ax (A := Tr_ww1) (by simp) (by simp)) <|
  .andR (A := Tr_nc0) (B := F7) (by simp) (.ax (A := Tr_nc0) (by simp) (by simp)) <|
  .andR (A := Tr_cw0) (B := F8) (by simp) (.ax (A := Tr_cw0) (by simp) (by simp)) <|
  .andR (A := Tr_wc0) (B := F9) (by simp) (.ax (A := Tr_wc0) (by simp) (by simp)) <|
  .andR (A := Sf_nn1) (B := F10) (by simp) (.ax (A := Sf_nn1) (by simp) (by simp)) <|
  .andR (A := Sf_wn1) (B := F11) (by simp) (.ax (A := Sf_wn1) (by simp) (by simp)) <|
  .andR (A := Sf_nw1) (B := F12) (by simp) (.ax (A := Sf_nw1) (by simp) (by simp)) <|
  .andR (A := Sf_cn0) (B := F13) (by simp) (.ax (A := Sf_cn0) (by simp) (by simp)) <|
  .andR (A := Sf_ww1) (B := F14) (by simp) (.ax (A := Sf_ww1) (by simp) (by simp)) <|
  .andR (A := Sf_nc0) (B := F15) (by simp) (.ax (A := Sf_nc0) (by simp) (by simp)) <|
  .andR (A := Sf_cw0) (B := Sf_wc0) (by simp) (.ax (A := Sf_cw0) (by simp) (by simp))
    (.ax (A := Sf_wc0) (by simp) (by simp))

theorem sm_inv : [D0, F1] ⊢ [Inv] :=
  .andR (A := D0) (B := F1) (by simp) (.ax (A := D0) (by simp) (by simp)) (.ax (A := F1) (by simp) (by simp))

theorem sm_exp (Γ' : List (Formula (P ⊕ St)))
    (h : Γ' ⊢ [at_ nn1, at_ wn1, at_ nw1, at_ cn0, at_ ww1, at_ nc0, at_ cw0, at_ wc0, ⊥ₗ]) : Γ' ⊢ [D0] :=
  .orR (A := at_ nn1) (B := D1) (by simp) <|
  .orR (A := at_ wn1) (B := D2) (by simp) <|
  .orR (A := at_ nw1) (B := D3) (by simp) <|
  .orR (A := at_ cn0) (B := D4) (by simp) <|
  .orR (A := at_ ww1) (B := D5) (by simp) <|
  .orR (A := at_ nc0) (B := D6) (by simp) <|
  .orR (A := at_ cw0) (B := D7) (by simp) <|
  .orR (A := at_ wc0) (B := ⊥ₗ) (by simp) <|
  .wk h (by simp) (by simp)

theorem sm_hN_nn1 : [N_nn1] ⊢ [D0] := sm_exp [N_nn1] <|
  .orL (A := at_ wn1) (B := at_ nw1 ⋎ ⊥ₗ) (by simp) (.ax (A := at_ wn1) (by simp) (by simp)) <|
  .orL (A := at_ nw1) (B := ⊥ₗ) (by simp) (.ax (A := at_ nw1) (by simp) (by simp)) (.botL (by simp))
theorem sm_hN_wn1 : [N_wn1] ⊢ [D0] := sm_exp [N_wn1] <|
  .orL (A := at_ cn0) (B := at_ ww1 ⋎ ⊥ₗ) (by simp) (.ax (A := at_ cn0) (by simp) (by simp)) <|
  .orL (A := at_ ww1) (B := ⊥ₗ) (by simp) (.ax (A := at_ ww1) (by simp) (by simp)) (.botL (by simp))
theorem sm_hN_nw1 : [N_nw1] ⊢ [D0] := sm_exp [N_nw1] <|
  .orL (A := at_ ww1) (B := at_ nc0 ⋎ ⊥ₗ) (by simp) (.ax (A := at_ ww1) (by simp) (by simp)) <|
  .orL (A := at_ nc0) (B := ⊥ₗ) (by simp) (.ax (A := at_ nc0) (by simp) (by simp)) (.botL (by simp))
theorem sm_hN_cn0 : [N_cn0] ⊢ [D0] := sm_exp [N_cn0] <|
  .orL (A := at_ nn1) (B := at_ cw0 ⋎ ⊥ₗ) (by simp) (.ax (A := at_ nn1) (by simp) (by simp)) <|
  .orL (A := at_ cw0) (B := ⊥ₗ) (by simp) (.ax (A := at_ cw0) (by simp) (by simp)) (.botL (by simp))
theorem sm_hN_ww1 : [N_ww1] ⊢ [D0] := sm_exp [N_ww1] <|
  .orL (A := at_ cw0) (B := at_ wc0 ⋎ ⊥ₗ) (by simp) (.ax (A := at_ cw0) (by simp) (by simp)) <|
  .orL (A := at_ wc0) (B := ⊥ₗ) (by simp) (.ax (A := at_ wc0) (by simp) (by simp)) (.botL (by simp))
theorem sm_hN_nc0 : [N_nc0] ⊢ [D0] := sm_exp [N_nc0] <|
  .orL (A := at_ wc0) (B := at_ nn1 ⋎ ⊥ₗ) (by simp) (.ax (A := at_ wc0) (by simp) (by simp)) <|
  .orL (A := at_ nn1) (B := ⊥ₗ) (by simp) (.ax (A := at_ nn1) (by simp) (by simp)) (.botL (by simp))
theorem sm_hN_cw0 : [N_cw0] ⊢ [D0] := sm_exp [N_cw0] <|
  .orL (A := at_ nw1) (B := ⊥ₗ) (by simp) (.ax (A := at_ nw1) (by simp) (by simp)) (.botL (by simp))
theorem sm_hN_wc0 : [N_wc0] ⊢ [D0] := sm_exp [N_wc0] <|
  .orL (A := at_ wn1) (B := ⊥ₗ) (by simp) (.ax (A := at_ wn1) (by simp) (by simp)) (.botL (by simp))

theorem sm_sq_nn1 : [at_ nn1, Tr_nn1] ⊢ [𝐗 D0] :=
  .alwaysL (A := at_ nn1 ⇒ 𝐗 N_nn1) (by simp) <|
  .impL (A := at_ nn1) (B := 𝐗 N_nn1) (by simp) (.ax (A := at_ nn1) (by simp) (by simp)) <|
  .step sm_hN_nn1 (by simp) (by simp)
theorem sm_sq_wn1 : [at_ wn1, Tr_wn1] ⊢ [𝐗 D0] :=
  .alwaysL (A := at_ wn1 ⇒ 𝐗 N_wn1) (by simp) <|
  .impL (A := at_ wn1) (B := 𝐗 N_wn1) (by simp) (.ax (A := at_ wn1) (by simp) (by simp)) <|
  .step sm_hN_wn1 (by simp) (by simp)
theorem sm_sq_nw1 : [at_ nw1, Tr_nw1] ⊢ [𝐗 D0] :=
  .alwaysL (A := at_ nw1 ⇒ 𝐗 N_nw1) (by simp) <|
  .impL (A := at_ nw1) (B := 𝐗 N_nw1) (by simp) (.ax (A := at_ nw1) (by simp) (by simp)) <|
  .step sm_hN_nw1 (by simp) (by simp)
theorem sm_sq_cn0 : [at_ cn0, Tr_cn0] ⊢ [𝐗 D0] :=
  .alwaysL (A := at_ cn0 ⇒ 𝐗 N_cn0) (by simp) <|
  .impL (A := at_ cn0) (B := 𝐗 N_cn0) (by simp) (.ax (A := at_ cn0) (by simp) (by simp)) <|
  .step sm_hN_cn0 (by simp) (by simp)
theorem sm_sq_ww1 : [at_ ww1, Tr_ww1] ⊢ [𝐗 D0] :=
  .alwaysL (A := at_ ww1 ⇒ 𝐗 N_ww1) (by simp) <|
  .impL (A := at_ ww1) (B := 𝐗 N_ww1) (by simp) (.ax (A := at_ ww1) (by simp) (by simp)) <|
  .step sm_hN_ww1 (by simp) (by simp)
theorem sm_sq_nc0 : [at_ nc0, Tr_nc0] ⊢ [𝐗 D0] :=
  .alwaysL (A := at_ nc0 ⇒ 𝐗 N_nc0) (by simp) <|
  .impL (A := at_ nc0) (B := 𝐗 N_nc0) (by simp) (.ax (A := at_ nc0) (by simp) (by simp)) <|
  .step sm_hN_nc0 (by simp) (by simp)
theorem sm_sq_cw0 : [at_ cw0, Tr_cw0] ⊢ [𝐗 D0] :=
  .alwaysL (A := at_ cw0 ⇒ 𝐗 N_cw0) (by simp) <|
  .impL (A := at_ cw0) (B := 𝐗 N_cw0) (by simp) (.ax (A := at_ cw0) (by simp) (by simp)) <|
  .step sm_hN_cw0 (by simp) (by simp)
theorem sm_sq_wc0 : [at_ wc0, Tr_wc0] ⊢ [𝐗 D0] :=
  .alwaysL (A := at_ wc0 ⇒ 𝐗 N_wc0) (by simp) <|
  .impL (A := at_ wc0) (B := 𝐗 N_wc0) (by simp) (.ax (A := at_ wc0) (by simp) (by simp)) <|
  .step sm_hN_wc0 (by simp) (by simp)

set_option maxHeartbeats 4000000 in
theorem sm_stepD : [D0, F1] ⊢ [𝐗 D0] :=
  .andL (A := Tr_nn1) (B := F2) (by simp) <|
  .andL (A := Tr_wn1) (B := F3) (by simp) <|
  .andL (A := Tr_nw1) (B := F4) (by simp) <|
  .andL (A := Tr_cn0) (B := F5) (by simp) <|
  .andL (A := Tr_ww1) (B := F6) (by simp) <|
  .andL (A := Tr_nc0) (B := F7) (by simp) <|
  .andL (A := Tr_cw0) (B := F8) (by simp) <|
  .andL (A := Tr_wc0) (B := F9) (by simp) <|
  .orL (A := at_ nn1) (B := D1) (by simp) (.wk sm_sq_nn1 (by simp) (by simp)) <|
  .orL (A := at_ wn1) (B := D2) (by simp) (.wk sm_sq_wn1 (by simp) (by simp)) <|
  .orL (A := at_ nw1) (B := D3) (by simp) (.wk sm_sq_nw1 (by simp) (by simp)) <|
  .orL (A := at_ cn0) (B := D4) (by simp) (.wk sm_sq_cn0 (by simp) (by simp)) <|
  .orL (A := at_ ww1) (B := D5) (by simp) (.wk sm_sq_ww1 (by simp) (by simp)) <|
  .orL (A := at_ nc0) (B := D6) (by simp) (.wk sm_sq_nc0 (by simp) (by simp)) <|
  .orL (A := at_ cw0) (B := D7) (by simp) (.wk sm_sq_cw0 (by simp) (by simp)) <|
  .orL (A := at_ wc0) (B := ⊥ₗ) (by simp) (.wk sm_sq_wc0 (by simp) (by simp))
    (.botL (by simp))

set_option maxHeartbeats 4000000 in
theorem sm_stepF : [F1] ⊢ [𝐗 F1] :=
  .andL (A := Tr_nn1) (B := F2) (by simp) <|
  .andL (A := Tr_wn1) (B := F3) (by simp) <|
  .andL (A := Tr_nw1) (B := F4) (by simp) <|
  .andL (A := Tr_cn0) (B := F5) (by simp) <|
  .andL (A := Tr_ww1) (B := F6) (by simp) <|
  .andL (A := Tr_nc0) (B := F7) (by simp) <|
  .andL (A := Tr_cw0) (B := F8) (by simp) <|
  .andL (A := Tr_wc0) (B := F9) (by simp) <|
  .andL (A := Sf_nn1) (B := F10) (by simp) <|
  .andL (A := Sf_wn1) (B := F11) (by simp) <|
  .andL (A := Sf_nw1) (B := F12) (by simp) <|
  .andL (A := Sf_cn0) (B := F13) (by simp) <|
  .andL (A := Sf_ww1) (B := F14) (by simp) <|
  .andL (A := Sf_nc0) (B := F15) (by simp) <|
  .andL (A := Sf_cw0) (B := Sf_wc0) (by simp) <|
  .alwaysL (A := at_ nn1 ⇒ 𝐗 N_nn1) (by simp) <|
  .alwaysL (A := at_ wn1 ⇒ 𝐗 N_wn1) (by simp) <|
  .alwaysL (A := at_ nw1 ⇒ 𝐗 N_nw1) (by simp) <|
  .alwaysL (A := at_ cn0 ⇒ 𝐗 N_cn0) (by simp) <|
  .alwaysL (A := at_ ww1 ⇒ 𝐗 N_ww1) (by simp) <|
  .alwaysL (A := at_ nc0 ⇒ 𝐗 N_nc0) (by simp) <|
  .alwaysL (A := at_ cw0 ⇒ 𝐗 N_cw0) (by simp) <|
  .alwaysL (A := at_ wc0 ⇒ 𝐗 N_wc0) (by simp) <|
  .alwaysL (A := at_ nn1 ⇒ ∼(ap crit1)) (by simp) <|
  .alwaysL (A := at_ wn1 ⇒ ∼(ap crit1)) (by simp) <|
  .alwaysL (A := at_ nw1 ⇒ ∼(ap crit1)) (by simp) <|
  .alwaysL (A := at_ cn0 ⇒ ∼(ap crit2)) (by simp) <|
  .alwaysL (A := at_ ww1 ⇒ ∼(ap crit1)) (by simp) <|
  .alwaysL (A := at_ nc0 ⇒ ∼(ap crit1)) (by simp) <|
  .alwaysL (A := at_ cw0 ⇒ ∼(ap crit2)) (by simp) <|
  .alwaysL (A := at_ wc0 ⇒ ∼(ap crit1)) (by simp) <|
  .step sm_lF (by simp) (by simp)

theorem sm_p2 : [Inv] ⊢ [𝐗 Inv] :=
  .andL (A := D0) (B := F1) (by simp) <|
  .cut (𝐗 D0) (.wk sm_stepD (by simp) (by simp)) <|
  .cut (𝐗 F1) (.wk sm_stepF (by simp) (by simp)) <|
  .step sm_inv (by simp) (by simp)

set_option maxHeartbeats 4000000 in
theorem sm_p3 : [Inv] ⊢ [∼(ap crit1 ⋏ ap crit2)] :=
  .andL (A := D0) (B := F1) (by simp) <|
  .andL (A := Tr_nn1) (B := F2) (by simp) <|
  .andL (A := Tr_wn1) (B := F3) (by simp) <|
  .andL (A := Tr_nw1) (B := F4) (by simp) <|
  .andL (A := Tr_cn0) (B := F5) (by simp) <|
  .andL (A := Tr_ww1) (B := F6) (by simp) <|
  .andL (A := Tr_nc0) (B := F7) (by simp) <|
  .andL (A := Tr_cw0) (B := F8) (by simp) <|
  .andL (A := Tr_wc0) (B := F9) (by simp) <|
  .andL (A := Sf_nn1) (B := F10) (by simp) <|
  .andL (A := Sf_wn1) (B := F11) (by simp) <|
  .andL (A := Sf_nw1) (B := F12) (by simp) <|
  .andL (A := Sf_cn0) (B := F13) (by simp) <|
  .andL (A := Sf_ww1) (B := F14) (by simp) <|
  .andL (A := Sf_nc0) (B := F15) (by simp) <|
  .andL (A := Sf_cw0) (B := Sf_wc0) (by simp) <|
  .negR (A := ap crit1 ⋏ ap crit2) (by simp) <|
  .andL (A := ap crit1) (B := ap crit2) (by simp) <|
  .orL (A := at_ nn1) (B := D1) (by simp)
    (.alwaysL (A := at_ nn1 ⇒ ∼(ap crit1)) (by simp) <|
      .impL (A := at_ nn1) (B := ∼(ap crit1)) (by simp) (.ax (A := at_ nn1) (by simp) (by simp)) <|
      .negL (A := ap crit1) (by simp) (.ax (A := ap crit1) (by simp) (by simp))) <|
  .orL (A := at_ wn1) (B := D2) (by simp)
    (.alwaysL (A := at_ wn1 ⇒ ∼(ap crit1)) (by simp) <|
      .impL (A := at_ wn1) (B := ∼(ap crit1)) (by simp) (.ax (A := at_ wn1) (by simp) (by simp)) <|
      .negL (A := ap crit1) (by simp) (.ax (A := ap crit1) (by simp) (by simp))) <|
  .orL (A := at_ nw1) (B := D3) (by simp)
    (.alwaysL (A := at_ nw1 ⇒ ∼(ap crit1)) (by simp) <|
      .impL (A := at_ nw1) (B := ∼(ap crit1)) (by simp) (.ax (A := at_ nw1) (by simp) (by simp)) <|
      .negL (A := ap crit1) (by simp) (.ax (A := ap crit1) (by simp) (by simp))) <|
  .orL (A := at_ cn0) (B := D4) (by simp)
    (.alwaysL (A := at_ cn0 ⇒ ∼(ap crit2)) (by simp) <|
      .impL (A := at_ cn0) (B := ∼(ap crit2)) (by simp) (.ax (A := at_ cn0) (by simp) (by simp)) <|
      .negL (A := ap crit2) (by simp) (.ax (A := ap crit2) (by simp) (by simp))) <|
  .orL (A := at_ ww1) (B := D5) (by simp)
    (.alwaysL (A := at_ ww1 ⇒ ∼(ap crit1)) (by simp) <|
      .impL (A := at_ ww1) (B := ∼(ap crit1)) (by simp) (.ax (A := at_ ww1) (by simp) (by simp)) <|
      .negL (A := ap crit1) (by simp) (.ax (A := ap crit1) (by simp) (by simp))) <|
  .orL (A := at_ nc0) (B := D6) (by simp)
    (.alwaysL (A := at_ nc0 ⇒ ∼(ap crit1)) (by simp) <|
      .impL (A := at_ nc0) (B := ∼(ap crit1)) (by simp) (.ax (A := at_ nc0) (by simp) (by simp)) <|
      .negL (A := ap crit1) (by simp) (.ax (A := ap crit1) (by simp) (by simp))) <|
  .orL (A := at_ cw0) (B := D7) (by simp)
    (.alwaysL (A := at_ cw0 ⇒ ∼(ap crit2)) (by simp) <|
      .impL (A := at_ cw0) (B := ∼(ap crit2)) (by simp) (.ax (A := at_ cw0) (by simp) (by simp)) <|
      .negL (A := ap crit2) (by simp) (.ax (A := ap crit2) (by simp) (by simp))) <|
  .orL (A := at_ wc0) (B := ⊥ₗ) (by simp)
    (.alwaysL (A := at_ wc0 ⇒ ∼(ap crit1)) (by simp) <|
      .impL (A := at_ wc0) (B := ∼(ap crit1)) (by simp) (.ax (A := at_ wc0) (by simp) (by simp)) <|
      .negL (A := ap crit1) (by simp) (.ax (A := ap crit1) (by simp) (by simp)))
    (.botL (by simp))

set_option maxHeartbeats 4000000 in
theorem sm_main : [(at_ nn1 ⋎ ⊥ₗ), Tr_nn1, Tr_wn1, Tr_nw1, Tr_cn0, Tr_ww1, Tr_nc0, Tr_cw0, Tr_wc0, Sf_nn1, Sf_wn1, Sf_nw1, Sf_cn0, Sf_ww1, Sf_nc0, Sf_cw0, Sf_wc0] ⊢ [𝐆 (∼(ap crit1 ⋏ ap crit2))] :=
  .alwaysR (A := ∼(ap crit1 ⋏ ap crit2)) Inv (by simp)
    (.andR (A := D0) (B := F1) (by simp)
      (.orL (A := at_ nn1) (B := ⊥ₗ) (by simp)
        (.orR (A := at_ nn1) (B := D1) (by simp) (.ax (A := at_ nn1) (by simp) (by simp)))
        (.botL (by simp)))
      (.wk sm_lF (by simp) (by simp)))
    sm_p2 sm_p3

set_option maxHeartbeats 4000000 in
theorem candidate : S.hyps ⊢ [lift specMutex] := by
  show [(at_ nn1 ⋎ ⊥ₗ), 𝐆 (at_ nn0 ⇒ ∼(ap crit1)), 𝐆 (at_ nn0 ⇒ ∼(ap crit2)), 𝐆 (at_ nn0 ⇒ 𝐗 (at_ wn0 ⋎ (at_ nw0 ⋎ ⊥ₗ))), 𝐆 (at_ nn1 ⇒ ∼(ap crit1)), 𝐆 (at_ nn1 ⇒ ∼(ap crit2)), 𝐆 (at_ nn1 ⇒ 𝐗 (at_ wn1 ⋎ (at_ nw1 ⋎ ⊥ₗ))), 𝐆 (at_ nw0 ⇒ ∼(ap crit1)), 𝐆 (at_ nw0 ⇒ ∼(ap crit2)), 𝐆 (at_ nw0 ⇒ 𝐗 (at_ ww0 ⋎ ⊥ₗ)), 𝐆 (at_ nw1 ⇒ ∼(ap crit1)), 𝐆 (at_ nw1 ⇒ ∼(ap crit2)), 𝐆 (at_ nw1 ⇒ 𝐗 (at_ ww1 ⋎ (at_ nc0 ⋎ ⊥ₗ))), 𝐆 (at_ nc0 ⇒ ap crit2), 𝐆 (at_ nc0 ⇒ ∼(ap crit1)), 𝐆 (at_ nc0 ⇒ 𝐗 (at_ wc0 ⋎ (at_ nn1 ⋎ ⊥ₗ))), 𝐆 (at_ nc1 ⇒ ap crit2), 𝐆 (at_ nc1 ⇒ ∼(ap crit1)), 𝐆 (at_ nc1 ⇒ 𝐗 (at_ wc1 ⋎ (at_ nn1 ⋎ ⊥ₗ))), 𝐆 (at_ wn0 ⇒ ∼(ap crit1)), 𝐆 (at_ wn0 ⇒ ∼(ap crit2)), 𝐆 (at_ wn0 ⇒ 𝐗 (at_ ww0 ⋎ ⊥ₗ)), 𝐆 (at_ wn1 ⇒ ∼(ap crit1)), 𝐆 (at_ wn1 ⇒ ∼(ap crit2)), 𝐆 (at_ wn1 ⇒ 𝐗 (at_ cn0 ⋎ (at_ ww1 ⋎ ⊥ₗ))), 𝐆 (at_ ww0 ⇒ ∼(ap crit1)), 𝐆 (at_ ww0 ⇒ ∼(ap crit2)), 𝐆 (at_ ww0 ⇒ 𝐗 (at_ ww0 ⋎ ⊥ₗ)), 𝐆 (at_ ww1 ⇒ ∼(ap crit1)), 𝐆 (at_ ww1 ⇒ ∼(ap crit2)), 𝐆 (at_ ww1 ⇒ 𝐗 (at_ cw0 ⋎ (at_ wc0 ⋎ ⊥ₗ))), 𝐆 (at_ wc0 ⇒ ap crit2), 𝐆 (at_ wc0 ⇒ ∼(ap crit1)), 𝐆 (at_ wc0 ⇒ 𝐗 (at_ wn1 ⋎ ⊥ₗ)), 𝐆 (at_ wc1 ⇒ ap crit2), 𝐆 (at_ wc1 ⇒ ∼(ap crit1)), 𝐆 (at_ wc1 ⇒ 𝐗 (at_ cc0 ⋎ (at_ wn1 ⋎ ⊥ₗ))), 𝐆 (at_ cn0 ⇒ ap crit1), 𝐆 (at_ cn0 ⇒ ∼(ap crit2)), 𝐆 (at_ cn0 ⇒ 𝐗 (at_ nn1 ⋎ (at_ cw0 ⋎ ⊥ₗ))), 𝐆 (at_ cn1 ⇒ ap crit1), 𝐆 (at_ cn1 ⇒ ∼(ap crit2)), 𝐆 (at_ cn1 ⇒ 𝐗 (at_ nn1 ⋎ (at_ cw1 ⋎ ⊥ₗ))), 𝐆 (at_ cw0 ⇒ ap crit1), 𝐆 (at_ cw0 ⇒ ∼(ap crit2)), 𝐆 (at_ cw0 ⇒ 𝐗 (at_ nw1 ⋎ ⊥ₗ)), 𝐆 (at_ cw1 ⇒ ap crit1), 𝐆 (at_ cw1 ⇒ ∼(ap crit2)), 𝐆 (at_ cw1 ⇒ 𝐗 (at_ nw1 ⋎ (at_ cc0 ⋎ ⊥ₗ))), 𝐆 (at_ cc0 ⇒ ap crit1), 𝐆 (at_ cc0 ⇒ ap crit2), 𝐆 (at_ cc0 ⇒ 𝐗 (at_ nc1 ⋎ (at_ cn1 ⋎ ⊥ₗ))), 𝐆 (at_ cc1 ⇒ ap crit1), 𝐆 (at_ cc1 ⇒ ap crit2), 𝐆 (at_ cc1 ⇒ 𝐗 (at_ nc1 ⋎ (at_ cn1 ⋎ ⊥ₗ)))] ⊢ [𝐆 (∼(ap crit1 ⋏ ap crit2))]
  exact .wk sm_main (by simp) (by simp)

end Candidate

theorem verified : Bench.Semaphore.S.Models Bench.Semaphore.specMutex :=
  Bench.Semaphore.S.sat_of_derives Candidate.candidate

#print axioms verified
