import Bench

open LTL LTL.System
open Bench.Vending
open Bench.Vending.P Bench.Vending.St

namespace Candidate

abbrev bd3 : Formula (P ⊕ St) := (at_ pay ⇒ 𝐗 (at_ select ⋎ ⊥ₗ))
abbrev bd6 : Formula (P ⊕ St) := (at_ select ⇒ 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ)))
abbrev bd8 : Formula (P ⊕ St) := (at_ soda ⇒ ap drink)
abbrev bd9 : Formula (P ⊕ St) := (at_ soda ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ))
abbrev bd11 : Formula (P ⊕ St) := (at_ beer ⇒ ap drink)
abbrev bd12 : Formula (P ⊕ St) := (at_ beer ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ))
abbrev fL3 : Formula (P ⊕ St) := (at_ soda ⋎ at_ beer)
abbrev fL2 : Formula (P ⊕ St) := (at_ select ⋎ fL3)
abbrev fLoc : Formula (P ⊕ St) := (at_ pay ⋎ fL2)
abbrev fR5 : Formula (P ⊕ St) := ((𝐆 bd12) ⋏ fLoc)
abbrev fR4 : Formula (P ⊕ St) := ((𝐆 bd11) ⋏ fR5)
abbrev fR3 : Formula (P ⊕ St) := ((𝐆 bd9) ⋏ fR4)
abbrev fR2 : Formula (P ⊕ St) := ((𝐆 bd8) ⋏ fR3)
abbrev fR1 : Formula (P ⊕ St) := ((𝐆 bd6) ⋏ fR2)
abbrev invF : Formula (P ⊕ St) := ((𝐆 bd3) ⋏ fR1)

theorem candidate : S.hyps ⊢ [lift specRecur] := by
  show [(at_ pay ⋎ ⊥ₗ), 𝐆 (at_ pay ⇒ ∼(ap paid)), 𝐆 (at_ pay ⇒ ∼(ap drink)), 𝐆 (at_ pay ⇒ 𝐗 (at_ select ⋎ ⊥ₗ)), 𝐆 (at_ select ⇒ ap paid), 𝐆 (at_ select ⇒ ∼(ap drink)), 𝐆 (at_ select ⇒ 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))), 𝐆 (at_ soda ⇒ ap paid), 𝐆 (at_ soda ⇒ ap drink), 𝐆 (at_ soda ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ)), 𝐆 (at_ beer ⇒ ap paid), 𝐆 (at_ beer ⇒ ap drink), 𝐆 (at_ beer ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ))] ⊢ [𝐆 𝐅 (ap drink)]
  have d1 : [𝐆 bd8, 𝐆 bd11, (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))] ⊢ [𝐅 (ap drink)] :=
    .alwaysL (A := bd8) (by simp) (.alwaysL (A := bd11) (by simp)
      (.evR (A := ap drink) (by simp)
        (.orL (A := at_ soda) (B := (at_ beer ⋎ ⊥ₗ)) (by simp)
          (.impL (A := at_ soda) (B := ap drink) (by simp) (.close (by decide)) (.close (by decide)))
          (.orL (A := at_ beer) (B := ⊥ₗ) (by simp)
            (.impL (A := at_ beer) (B := ap drink) (by simp) (.close (by decide)) (.close (by decide)))
            (.botL (by simp))))))
  have d2 : [𝐆 bd6, 𝐆 bd8, 𝐆 bd11, (at_ select ⋎ ⊥ₗ)] ⊢ [𝐅 (ap drink)] :=
    .alwaysL (A := bd6) (by simp) (.alwaysL (A := bd8) (by simp) (.alwaysL (A := bd11) (by simp)
      (.orL (A := at_ select) (B := ⊥ₗ) (by simp)
        (.impL (A := at_ select) (B := 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))) (by simp) (.close (by decide))
          (.evR (A := ap drink) (by simp)
            (.step (B := 𝐅 (ap drink)) d1 (by simp) (by simp))))
        (.botL (by simp)))))
  have bPay : [𝐆 bd3, 𝐆 bd6, 𝐆 bd8, 𝐆 bd9, 𝐆 bd11, 𝐆 bd12, (at_ pay ⋎ ⊥ₗ)] ⊢ [invF] :=
    .andR (A := 𝐆 bd3) (B := fR1) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd6) (B := fR2) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd8) (B := fR3) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd9) (B := fR4) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd11) (B := fR5) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd12) (B := fLoc) (by simp) (.close (by decide)) <|
    .orL (A := at_ pay) (B := ⊥ₗ) (by simp)
      (.orR (A := at_ pay) (B := fL2) (by simp) (.close (by decide)))
      (.botL (by simp))
  have bSel : [𝐆 bd3, 𝐆 bd6, 𝐆 bd8, 𝐆 bd9, 𝐆 bd11, 𝐆 bd12, (at_ select ⋎ ⊥ₗ)] ⊢ [invF] :=
    .andR (A := 𝐆 bd3) (B := fR1) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd6) (B := fR2) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd8) (B := fR3) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd9) (B := fR4) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd11) (B := fR5) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd12) (B := fLoc) (by simp) (.close (by decide)) <|
    .orL (A := at_ select) (B := ⊥ₗ) (by simp)
      (.orR (A := at_ pay) (B := fL2) (by simp)
        (.orR (A := at_ select) (B := fL3) (by simp) (.close (by decide))))
      (.botL (by simp))
  have bSB : [𝐆 bd3, 𝐆 bd6, 𝐆 bd8, 𝐆 bd9, 𝐆 bd11, 𝐆 bd12, (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))] ⊢ [invF] :=
    .andR (A := 𝐆 bd3) (B := fR1) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd6) (B := fR2) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd8) (B := fR3) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd9) (B := fR4) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd11) (B := fR5) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd12) (B := fLoc) (by simp) (.close (by decide)) <|
    .orL (A := at_ soda) (B := (at_ beer ⋎ ⊥ₗ)) (by simp)
      (.orR (A := at_ pay) (B := fL2) (by simp)
        (.orR (A := at_ select) (B := fL3) (by simp)
          (.orR (A := at_ soda) (B := at_ beer) (by simp) (.close (by decide)))))
      (.orL (A := at_ beer) (B := ⊥ₗ) (by simp)
        (.orR (A := at_ pay) (B := fL2) (by simp)
          (.orR (A := at_ select) (B := fL3) (by simp)
            (.orR (A := at_ soda) (B := at_ beer) (by simp) (.close (by decide)))))
        (.botL (by simp)))
  have h0 : [(at_ pay ⋎ ⊥ₗ), 𝐆 (at_ pay ⇒ ∼(ap paid)), 𝐆 (at_ pay ⇒ ∼(ap drink)), 𝐆 (at_ pay ⇒ 𝐗 (at_ select ⋎ ⊥ₗ)), 𝐆 (at_ select ⇒ ap paid), 𝐆 (at_ select ⇒ ∼(ap drink)), 𝐆 (at_ select ⇒ 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))), 𝐆 (at_ soda ⇒ ap paid), 𝐆 (at_ soda ⇒ ap drink), 𝐆 (at_ soda ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ)), 𝐆 (at_ beer ⇒ ap paid), 𝐆 (at_ beer ⇒ ap drink), 𝐆 (at_ beer ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ))] ⊢ [invF, 𝐆 𝐅 (ap drink)] :=
    .andR (A := 𝐆 bd3) (B := fR1) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd6) (B := fR2) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd8) (B := fR3) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd9) (B := fR4) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd11) (B := fR5) (by simp) (.close (by decide)) <|
    .andR (A := 𝐆 bd12) (B := fLoc) (by simp) (.close (by decide)) <|
    .orL (A := at_ pay) (B := ⊥ₗ) (by simp)
      (.orR (A := at_ pay) (B := fL2) (by simp) (.close (by decide)))
      (.botL (by simp))
  have h1 : [invF] ⊢ [𝐗 invF] :=
    .andL (A := 𝐆 bd3) (B := fR1) (by simp) <|
    .andL (A := 𝐆 bd6) (B := fR2) (by simp) <|
    .andL (A := 𝐆 bd8) (B := fR3) (by simp) <|
    .andL (A := 𝐆 bd9) (B := fR4) (by simp) <|
    .andL (A := 𝐆 bd11) (B := fR5) (by simp) <|
    .andL (A := 𝐆 bd12) (B := fLoc) (by simp) <|
    .alwaysL (A := bd3) (by simp) <|
    .alwaysL (A := bd6) (by simp) <|
    .alwaysL (A := bd8) (by simp) <|
    .alwaysL (A := bd9) (by simp) <|
    .alwaysL (A := bd11) (by simp) <|
    .alwaysL (A := bd12) (by simp) <|
    .orL (A := at_ pay) (B := fL2) (by simp)
      (.impL (A := at_ pay) (B := 𝐗 (at_ select ⋎ ⊥ₗ)) (by simp) (.close (by decide))
        (.step (B := invF) bSel (by simp) (by simp)))
      (.orL (A := at_ select) (B := fL3) (by simp)
        (.impL (A := at_ select) (B := 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))) (by simp) (.close (by decide))
          (.step (B := invF) bSB (by simp) (by simp)))
        (.orL (A := at_ soda) (B := at_ beer) (by simp)
          (.impL (A := at_ soda) (B := 𝐗 (at_ pay ⋎ ⊥ₗ)) (by simp) (.close (by decide))
            (.step (B := invF) bPay (by simp) (by simp)))
          (.impL (A := at_ beer) (B := 𝐗 (at_ pay ⋎ ⊥ₗ)) (by simp) (.close (by decide))
            (.step (B := invF) bPay (by simp) (by simp)))))
  have h2 : [invF] ⊢ [𝐅 (ap drink)] :=
    .andL (A := 𝐆 bd3) (B := fR1) (by simp) <|
    .andL (A := 𝐆 bd6) (B := fR2) (by simp) <|
    .andL (A := 𝐆 bd8) (B := fR3) (by simp) <|
    .andL (A := 𝐆 bd9) (B := fR4) (by simp) <|
    .andL (A := 𝐆 bd11) (B := fR5) (by simp) <|
    .andL (A := 𝐆 bd12) (B := fLoc) (by simp) <|
    .alwaysL (A := bd3) (by simp) <|
    .alwaysL (A := bd6) (by simp) <|
    .alwaysL (A := bd8) (by simp) <|
    .alwaysL (A := bd11) (by simp) <|
    .orL (A := at_ pay) (B := fL2) (by simp)
      (.impL (A := at_ pay) (B := 𝐗 (at_ select ⋎ ⊥ₗ)) (by simp) (.close (by decide))
        (.evR (A := ap drink) (by simp)
          (.step (B := 𝐅 (ap drink)) d2 (by simp) (by simp))))
      (.orL (A := at_ select) (B := fL3) (by simp)
        (.impL (A := at_ select) (B := 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))) (by simp) (.close (by decide))
          (.evR (A := ap drink) (by simp)
            (.step (B := 𝐅 (ap drink)) d1 (by simp) (by simp))))
        (.orL (A := at_ soda) (B := at_ beer) (by simp)
          (.evR (A := ap drink) (by simp)
            (.impL (A := at_ soda) (B := ap drink) (by simp) (.close (by decide)) (.close (by decide))))
          (.evR (A := ap drink) (by simp)
            (.impL (A := at_ beer) (B := ap drink) (by simp) (.close (by decide)) (.close (by decide))))))
  exact Derives.alwaysR (A := 𝐅 (ap drink)) (I := invF) (by simp) h0 h1 h2

end Candidate

theorem verified : Bench.Vending.S.Models Bench.Vending.specRecur :=
  Bench.Vending.S.sat_of_derives Candidate.candidate

#print axioms verified
