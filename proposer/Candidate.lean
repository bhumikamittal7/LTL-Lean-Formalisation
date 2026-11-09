import LTL

/-!
Paste the proposer's answer below, replacing `candidate`, then run

    lake env lean proposer/Candidate.lean

No output means Lean accepted the proof, and the last line then gives
`S ⊨ spec`. Otherwise, send the error messages back to the proposer.

The proof below is a reference answer for the running example, in the format
the prompt asks for.
-/

open LTL LTL.System
open LTL.Example (S spec P St)
open LTL.Example.P LTL.Example.St

namespace Candidate

-- invariant: in q1, together with the facts about q1
abbrev N : Formula (P ⊕ St) := at_ q1 ⋎ ⊥ₗ
abbrev T : Formula (P ⊕ St) := 𝐆 (at_ q1 ⇒ 𝐗 N)
abbrev D : Formula (P ⊕ St) := 𝐆 (at_ q1 ⇒ ap done)
abbrev I : Formula (P ⊕ St) := N ⋏ (T ⋏ D)

theorem candidate : S.hyps ⊢ [lift spec] := by
  show [(at_ q0 ⋎ ⊥ₗ), 𝐆 (at_ q0 ⇒ ap wait), 𝐆 (at_ q0 ⇒ ∼(ap done)),
        𝐆 (at_ q0 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ)), 𝐆 (at_ q1 ⇒ ap done),
        𝐆 (at_ q1 ⇒ ∼(ap wait)), 𝐆 (at_ q1 ⇒ 𝐗 (at_ q1 ⋎ ⊥ₗ))] ⊢ [𝐅 (𝐆 (ap done))]
  -- (O1) the invariant holds, given its parts
  have ob1 : [N, T, D] ⊢ [I, 𝐆 (ap done), 𝐗 (𝐅 (𝐆 (ap done))), 𝐅 (𝐆 (ap done))] :=
    .andR (A := N) (B := T ⋏ D) (by simp) (.close (by decide))
      (.andR (A := T) (B := D) (by simp) (.close (by decide)) (.close (by decide)))
  -- (O2) one step preserves the invariant
  have ob2 : [I] ⊢ [𝐗 I] :=
    .andL (A := N) (B := T ⋏ D) (by simp) <|
    .andL (A := T) (B := D) (by simp) <|
    .alwaysL (A := at_ q1 ⇒ 𝐗 N) (by simp) <|
    .alwaysL (A := at_ q1 ⇒ ap done) (by simp) <|
    .orL (A := at_ q1) (B := ⊥ₗ) (by simp)
      (.impL (A := at_ q1) (B := 𝐗 N) (by simp) (.close (by decide))
        (Derives.step (Γ' := [N, T, D]) (B := I)
          (.andR (A := N) (B := T ⋏ D) (by simp) (.close (by decide))
            (.andR (A := T) (B := D) (by simp) (.close (by decide)) (.close (by decide))))
          (by simp) (by simp)))
      (.botL (by simp))
  -- (O3) the invariant implies done
  have ob3 : [I] ⊢ [ap done] :=
    .andL (A := N) (B := T ⋏ D) (by simp) <|
    .andL (A := T) (B := D) (by simp) <|
    .alwaysL (A := at_ q1 ⇒ ap done) (by simp) <|
    .orL (A := at_ q1) (B := ⊥ₗ) (by simp)
      (.impL (A := at_ q1) (B := ap done) (by simp) (.close (by decide)) (.close (by decide)))
      (.botL (by simp))
  -- at position 1: F G done by the invariant rule
  have pos1 : [N, T, D] ⊢ [𝐅 (𝐆 (ap done))] :=
    .evR (A := 𝐆 (ap done)) (by simp) <|
    .alwaysR (A := ap done) I (by simp) ob1 ob2 ob3
  -- at position 0: unfold F, move to position 1
  exact
    .evR (A := 𝐆 (ap done)) (by simp) <|
    .orL (A := at_ q0) (B := ⊥ₗ) (by simp)
      (.alwaysL (A := at_ q0 ⇒ 𝐗 N) (by simp) <|
       .alwaysL (A := at_ q1 ⇒ 𝐗 N) (by simp) <|
       .alwaysL (A := at_ q1 ⇒ ap done) (by simp) <|
       .impL (A := at_ q0) (B := 𝐗 N) (by simp) (.close (by decide)) <|
       Derives.step (Γ' := [N, T, D]) pos1 (by simp) (by simp))
      (.botL (by simp))

/-- Lean accepted the candidate, so every trace of `S` satisfies `spec`. -/
theorem verified : S.Models spec := S.sat_of_derives candidate

end Candidate
