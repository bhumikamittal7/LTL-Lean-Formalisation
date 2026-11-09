import Bench

open LTL LTL.System
open Bench.Vending
open Bench.Vending.P Bench.Vending.St

namespace Candidate

abbrev sF : Formula (P ⊕ St) := at_ pay ⋎ (at_ select ⋎ (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ)))
abbrev vG1 : Formula (P ⊕ St) := 𝐆 (at_ pay ⇒ ∼(ap paid))
abbrev vG3 : Formula (P ⊕ St) := 𝐆 (at_ pay ⇒ 𝐗 (at_ select ⋎ ⊥ₗ))
abbrev vG6 : Formula (P ⊕ St) := 𝐆 (at_ select ⇒ 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ)))
abbrev vG8 : Formula (P ⊕ St) := 𝐆 (at_ soda ⇒ ap drink)
abbrev vG9 : Formula (P ⊕ St) := 𝐆 (at_ soda ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ))
abbrev vG11 : Formula (P ⊕ St) := 𝐆 (at_ beer ⇒ ap drink)
abbrev vG12 : Formula (P ⊕ St) := 𝐆 (at_ beer ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ))
abbrev r6 : Formula (P ⊕ St) := vG11 ⋏ vG12
abbrev r5 : Formula (P ⊕ St) := vG9 ⋏ r6
abbrev r4 : Formula (P ⊕ St) := vG8 ⋏ r5
abbrev r3 : Formula (P ⊕ St) := vG6 ⋏ r4
abbrev r2 : Formula (P ⊕ St) := vG3 ⋏ r3
abbrev r1 : Formula (P ⊕ St) := vG1 ⋏ r2
abbrev Inv : Formula (P ⊕ St) := sF ⋏ r1

theorem candidate : S.hyps ⊢ [lift specResp] := by
  show [(at_ pay ⋎ ⊥ₗ), 𝐆 (at_ pay ⇒ ∼(ap paid)), 𝐆 (at_ pay ⇒ ∼(ap drink)), 𝐆 (at_ pay ⇒ 𝐗 (at_ select ⋎ ⊥ₗ)), 𝐆 (at_ select ⇒ ap paid), 𝐆 (at_ select ⇒ ∼(ap drink)), 𝐆 (at_ select ⇒ 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))), 𝐆 (at_ soda ⇒ ap paid), 𝐆 (at_ soda ⇒ ap drink), 𝐆 (at_ soda ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ)), 𝐆 (at_ beer ⇒ ap paid), 𝐆 (at_ beer ⇒ ap drink), 𝐆 (at_ beer ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ))] ⊢ [𝐆 (ap paid ⇒ 𝐅 (ap drink))]
  have pS : ([at_ pay ⋎ ⊥ₗ] ⊢ [sF]) :=
    .orL (A := at_ pay) (B := ⊥ₗ) (by simp)
      (.orR (A := at_ pay) (B := at_ select ⋎ (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))) (by simp)
        (.close (by decide)))
      (.botL (by simp))
  have sS : ([at_ select ⋎ ⊥ₗ] ⊢ [sF]) :=
    .orL (A := at_ select) (B := ⊥ₗ) (by simp)
      (.orR (A := at_ pay) (B := at_ select ⋎ (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))) (by simp)
        (.orR (A := at_ select) (B := at_ soda ⋎ (at_ beer ⋎ ⊥ₗ)) (by simp)
          (.close (by decide))))
      (.botL (by simp))
  have dS : ([at_ soda ⋎ (at_ beer ⋎ ⊥ₗ)] ⊢ [sF]) :=
    .orR (A := at_ pay) (B := at_ select ⋎ (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))) (by simp)
      (.orR (A := at_ select) (B := at_ soda ⋎ (at_ beer ⋎ ⊥ₗ)) (by simp)
        (.close (by decide)))
  have hR : ([vG1, vG3, vG6, vG8, vG9, vG11, vG12] ⊢ [r1]) :=
    .andR (A := vG1) (B := r2) (by simp) (.close (by decide))
     (.andR (A := vG3) (B := r3) (by simp) (.close (by decide))
      (.andR (A := vG6) (B := r4) (by simp) (.close (by decide))
       (.andR (A := vG8) (B := r5) (by simp) (.close (by decide))
        (.andR (A := vG9) (B := r6) (by simp) (.close (by decide))
         (.andR (A := vG11) (B := vG12) (by simp) (.close (by decide)) (.close (by decide)))))))
  have hUp : ∀ φ : Formula (P ⊕ St), ([φ] ⊢ [sF]) →
      ((φ :: [vG1, vG3, vG6, vG8, vG9, vG11, vG12]) ⊢ [Inv]) := fun φ h =>
    .andR (A := sF) (B := r1) (by simp)
      (.wk h (by simp) (by simp))
      (.wk hR (by simp) (by simp))
  have hDec : ∀ Δ : List (Formula (P ⊕ St)),
      ([sF, vG1, vG3, vG6, vG8, vG9, vG11, vG12] ⊢ Δ) → ([Inv] ⊢ Δ) := fun Δ h =>
    .andL (A := sF) (B := r1) (by simp)
     (.andL (A := vG1) (B := r2) (by simp)
      (.andL (A := vG3) (B := r3) (by simp)
       (.andL (A := vG6) (B := r4) (by simp)
        (.andL (A := vG8) (B := r5) (by simp)
         (.andL (A := vG9) (B := r6) (by simp)
          (.andL (A := vG11) (B := vG12) (by simp)
            (.wk h (by simp) (fun _ hx => hx))))))))
  have hF : ([at_ soda ⋎ (at_ beer ⋎ ⊥ₗ), vG8, vG11] ⊢ [𝐅 (ap drink)]) :=
    .evR (A := ap drink) (by simp)
     (.alwaysL (A := at_ soda ⇒ ap drink) (by simp)
      (.alwaysL (A := at_ beer ⇒ ap drink) (by simp)
       (.orL (A := at_ soda) (B := at_ beer ⋎ ⊥ₗ) (by simp)
         (.impL (A := at_ soda) (B := ap drink) (by simp) (.close (by decide)) (.close (by decide)))
         (.orL (A := at_ beer) (B := ⊥ₗ) (by simp)
           (.impL (A := at_ beer) (B := ap drink) (by simp) (.close (by decide)) (.close (by decide)))
           (.botL (by simp))))))
  have hBcore : ∀ Γ : List (Formula (P ⊕ St)),
      (sF ∈ Γ) →
      ((at_ pay ⇒ 𝐗 (at_ select ⋎ ⊥ₗ)) ∈ Γ) →
      ((at_ select ⇒ 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))) ∈ Γ) →
      ((at_ soda ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ)) ∈ Γ) →
      ((at_ beer ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ)) ∈ Γ) →
      (𝐗 vG1 ∈ Γ) → (𝐗 vG3 ∈ Γ) → (𝐗 vG6 ∈ Γ) → (𝐗 vG8 ∈ Γ) →
      (𝐗 vG9 ∈ Γ) → (𝐗 vG11 ∈ Γ) → (𝐗 vG12 ∈ Γ) →
      (Γ ⊢ [𝐗 Inv]) := by
    intro Γ h0 h3 h6 h9 h12 x1 x3 x6 x8 x9 x11 x12
    have stepTo : ∀ φ : Formula (P ⊕ St), ([φ] ⊢ [sF]) →
        ∀ Γ₂ : List (Formula (P ⊕ St)), (𝐗 φ ∈ Γ₂) → (∀ x ∈ Γ, x ∈ Γ₂) → (Γ₂ ⊢ [𝐗 Inv]) := by
      intro φ hφ Γ₂ hx hsub
      exact .step (Γ' := φ :: [vG1, vG3, vG6, vG8, vG9, vG11, vG12]) (B := Inv)
        (hUp φ hφ)
        (by
          intro A hA
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
          rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hx
          · exact hsub _ x1
          · exact hsub _ x3
          · exact hsub _ x6
          · exact hsub _ x8
          · exact hsub _ x9
          · exact hsub _ x11
          · exact hsub _ x12)
        (by simp)
    exact .orL (A := at_ pay) (B := at_ select ⋎ (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))) h0
      (.impL (A := at_ pay) (B := 𝐗 (at_ select ⋎ ⊥ₗ)) (List.mem_cons_of_mem _ h3)
        (.close (by simp))
        (stepTo _ sS _ (by simp) (fun x hx => by simp [hx])))
      (.orL (A := at_ select) (B := at_ soda ⋎ (at_ beer ⋎ ⊥ₗ)) (by simp)
        (.impL (A := at_ select) (B := 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ)))
          (by simp [h6])
          (.close (by simp))
          (stepTo _ dS _ (by simp) (fun x hx => by simp [hx])))
        (.orL (A := at_ soda) (B := at_ beer ⋎ ⊥ₗ) (by simp)
          (.impL (A := at_ soda) (B := 𝐗 (at_ pay ⋎ ⊥ₗ))
            (by simp [h9])
            (.close (by simp))
            (stepTo _ pS _ (by simp) (fun x hx => by simp [hx])))
          (.orL (A := at_ beer) (B := ⊥ₗ) (by simp)
            (.impL (A := at_ beer) (B := 𝐗 (at_ pay ⋎ ⊥ₗ))
              (by simp [h12])
              (.close (by simp))
              (stepTo _ pS _ (by simp) (fun x hx => by simp [hx])))
            (.botL (by simp)))))
  have hB : ([sF, vG1, vG3, vG6, vG8, vG9, vG11, vG12] ⊢ [𝐗 Inv]) :=
    .alwaysL (A := at_ pay ⇒ ∼(ap paid)) (by simp)
    (.alwaysL (A := at_ pay ⇒ 𝐗 (at_ select ⋎ ⊥ₗ)) (by simp)
    (.alwaysL (A := at_ select ⇒ 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))) (by simp)
    (.alwaysL (A := at_ soda ⇒ ap drink) (by simp)
    (.alwaysL (A := at_ soda ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ)) (by simp)
    (.alwaysL (A := at_ beer ⇒ ap drink) (by simp)
    (.alwaysL (A := at_ beer ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ)) (by simp)
    (hBcore _ (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))))))
  have hC : ([sF, vG1, vG3, vG6, vG8, vG9, vG11, vG12] ⊢ [ap paid ⇒ 𝐅 (ap drink)]) :=
    .impR (A := ap paid) (B := 𝐅 (ap drink)) (by simp)
    (.alwaysL (A := at_ pay ⇒ ∼(ap paid)) (by simp)
    (.alwaysL (A := at_ select ⇒ 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))) (by simp)
    (.alwaysL (A := at_ soda ⇒ ap drink) (by simp)
    (.alwaysL (A := at_ beer ⇒ ap drink) (by simp)
    (.orL (A := at_ pay) (B := at_ select ⋎ (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))) (by simp)
      (.impL (A := at_ pay) (B := ∼(ap paid)) (by simp) (.close (by decide))
        (.negL (A := ap paid) (by simp) (.close (by decide))))
      (.orL (A := at_ select) (B := at_ soda ⋎ (at_ beer ⋎ ⊥ₗ)) (by simp)
        (.impL (A := at_ select) (B := 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))) (by simp) (.close (by decide))
          (.evR (A := ap drink) (by simp)
            (.step (Γ' := [at_ soda ⋎ (at_ beer ⋎ ⊥ₗ), vG8, vG11]) (B := 𝐅 (ap drink))
              hF (by simp) (by simp))))
        (.orL (A := at_ soda) (B := at_ beer ⋎ ⊥ₗ) (by simp)
          (.impL (A := at_ soda) (B := ap drink) (by simp) (.close (by decide))
            (.evR (A := ap drink) (by simp) (.close (by decide))))
          (.orL (A := at_ beer) (B := ⊥ₗ) (by simp)
            (.impL (A := at_ beer) (B := ap drink) (by simp) (.close (by decide))
              (.evR (A := ap drink) (by simp) (.close (by decide))))
            (.botL (by simp))))))))))
  exact .alwaysR (A := ap paid ⇒ 𝐅 (ap drink)) Inv (by simp)
    (.andR (A := sF) (B := r1) (by simp)
      (.wk pS (by simp) (by simp))
      (.wk hR (by simp) (by simp)))
    (hDec _ hB) (hDec _ hC)

end Candidate

theorem verified : Bench.Vending.S.Models Bench.Vending.specResp :=
  Bench.Vending.S.sat_of_derives Candidate.candidate

#print axioms verified
