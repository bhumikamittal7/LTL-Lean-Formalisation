import Bench

open LTL LTL.System
open Bench.Vending
open Bench.Vending.P Bench.Vending.St

namespace Candidate

theorem candidate : S.hyps ⊢ [lift specPrec] := by
  show [(at_ pay ⋎ ⊥ₗ), 𝐆 (at_ pay ⇒ ∼(ap paid)), 𝐆 (at_ pay ⇒ ∼(ap drink)), 𝐆 (at_ pay ⇒ 𝐗 (at_ select ⋎ ⊥ₗ)), 𝐆 (at_ select ⇒ ap paid), 𝐆 (at_ select ⇒ ∼(ap drink)), 𝐆 (at_ select ⇒ 𝐗 (at_ soda ⋎ (at_ beer ⋎ ⊥ₗ))), 𝐆 (at_ soda ⇒ ap paid), 𝐆 (at_ soda ⇒ ap drink), 𝐆 (at_ soda ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ)), 𝐆 (at_ beer ⇒ ap paid), 𝐆 (at_ beer ⇒ ap drink), 𝐆 (at_ beer ⇒ 𝐗 (at_ pay ⋎ ⊥ₗ))] ⊢ [(∼(ap drink) 𝐔 ap paid)]
  exact
    .orL (A := at_ pay) (B := ⊥ₗ) (by simp)
      (.untilR (A := ∼(ap drink)) (B := ap paid) (by simp)
        (.alwaysL (A := at_ pay ⇒ ∼(ap drink)) (by simp)
          (.impL (A := at_ pay) (B := ∼(ap drink)) (by simp)
            (.close (by decide))
            (.close (by decide))))
        (.alwaysL (A := at_ pay ⇒ 𝐗 (at_ select ⋎ ⊥ₗ)) (by simp)
          (.alwaysL (A := at_ select ⇒ ap paid) (by simp)
            (.impL (A := at_ pay) (B := 𝐗 (at_ select ⋎ ⊥ₗ)) (by simp)
              (.close (by decide))
              (.step (Γ' := [at_ select ⋎ ⊥ₗ, 𝐆 (at_ select ⇒ ap paid)])
                (B := ∼(ap drink) 𝐔 ap paid)
                (.orL (A := at_ select) (B := ⊥ₗ) (by simp)
                  (.alwaysL (A := at_ select ⇒ ap paid) (by simp)
                    (.impL (A := at_ select) (B := ap paid) (by simp)
                      (.close (by decide))
                      (.untilR (A := ∼(ap drink)) (B := ap paid) (by simp)
                        (.close (by decide))
                        (.close (by decide)))))
                  (.botL (by simp)))
                (by simp) (by simp))))))
      (.botL (by simp))

end Candidate

theorem verified : Bench.Vending.S.Models Bench.Vending.specPrec :=
  Bench.Vending.S.sat_of_derives Candidate.candidate

#print axioms verified
