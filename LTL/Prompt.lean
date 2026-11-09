import LTL.System

/-!
# Proposer prompt

`System.prompt` turns a verification problem `S ⊨ φ` into a text prompt for a
language model (or a person). The answer should be a Lean term proving
`S.hyps ⊢ [lift φ]`; paste it into `proposer/Candidate.lean` and run Lean.
-/

namespace LTL

namespace Formula

variable {AP : Type}

/-- Parenthesise the rendering `s` of `φ` when `φ` is the argument of a prefix
operator. Binary formulas are already rendered with parentheses. -/
def wrap : Formula AP → String → String
  | .bot, s | .and .., s | .or .., s | .imp .., s | .until .., s => s
  | _, s => s!"({s})"

/-- Render a formula in the library's Lean notation. -/
def toLean (atom : AP → String) : Formula AP → String
  | .atom p => atom p
  | .bot => "⊥ₗ"
  | .neg φ => s!"∼{wrap φ (toLean atom φ)}"
  | .and φ ψ => s!"({toLean atom φ} ⋏ {toLean atom ψ})"
  | .or φ ψ => s!"({toLean atom φ} ⋎ {toLean atom ψ})"
  | .imp φ ψ => s!"({toLean atom φ} ⇒ {toLean atom ψ})"
  | .next φ => s!"𝐗 {wrap φ (toLean atom φ)}"
  | .always φ => s!"𝐆 {wrap φ (toLean atom φ)}"
  | .eventually φ => s!"𝐅 {wrap φ (toLean atom φ)}"
  | .until φ ψ => s!"({toLean atom φ} 𝐔 {toLean atom ψ})"

end Formula

namespace System

variable {AP Q : Type} [DecidableEq AP] (S : System AP Q)

/-- The rules, as they appear to the proposer. Keep in sync with `LTL/Sequent.lean`. -/
def rulesText : String := "
Sequents are `Γ ⊢ Δ` with lists Γ, Δ. A rule names its principal formula by
membership and keeps it in the premise. Premises are listed in order.
Primitive connectives: ⊥ ∼ ⋏ ⇒ 𝐗 𝐆 𝐔. Abbreviations: ⊤ₗ = ∼⊥ₗ, A ⋎ B = ∼A ⇒ B,
𝐅 A = ⊤ₗ 𝐔 A.

Primitive rules (constructors of `Derives`):
  ax      : A ∈ Γ → A ∈ Δ → Γ ⊢ Δ
  botL    : ⊥ₗ ∈ Γ → Γ ⊢ Δ
  negL    : (∼A) ∈ Γ → Γ ⊢ A :: Δ → Γ ⊢ Δ
  negR    : (∼A) ∈ Δ → A :: Γ ⊢ Δ → Γ ⊢ Δ
  andL    : (A ⋏ B) ∈ Γ → A :: B :: Γ ⊢ Δ → Γ ⊢ Δ
  andR    : (A ⋏ B) ∈ Δ → Γ ⊢ A :: Δ → Γ ⊢ B :: Δ → Γ ⊢ Δ
  impL    : (A ⇒ B) ∈ Γ → Γ ⊢ A :: Δ → B :: Γ ⊢ Δ → Γ ⊢ Δ
  impR    : (A ⇒ B) ∈ Δ → A :: Γ ⊢ B :: Δ → Γ ⊢ Δ
  cut A   : Γ ⊢ A :: Δ → A :: Γ ⊢ Δ → Γ ⊢ Δ
  next    : Γ' ⊢ Δ' → (∀ A ∈ Γ', 𝐗 A ∈ Γ) → (∀ B ∈ Δ', 𝐗 B ∈ Δ) → Γ ⊢ Δ
  alwaysL : (𝐆 A) ∈ Γ → A :: 𝐗 (𝐆 A) :: Γ ⊢ Δ → Γ ⊢ Δ
  alwaysR I : (𝐆 A) ∈ Δ → Γ ⊢ I :: Δ → [I] ⊢ [𝐗 I] → [I] ⊢ [A] → Γ ⊢ Δ
  untilL I : (A 𝐔 B) ∈ Γ → [B] ⊢ [I] → [A, 𝐗 I] ⊢ [I] → I :: Γ ⊢ Δ → Γ ⊢ Δ
  untilR  : (A 𝐔 B) ∈ Δ → Γ ⊢ B :: A :: Δ → Γ ⊢ B :: 𝐗 (A 𝐔 B) :: Δ → Γ ⊢ Δ

Derived rules (theorems in namespace `Derives`):
  wk      : Γ ⊢ Δ → (∀ x ∈ Γ, x ∈ Γ') → (∀ x ∈ Δ, x ∈ Δ') → Γ' ⊢ Δ'
  step (Γ' := L) : L ⊢ [B] → (∀ A ∈ L, 𝐗 A ∈ Γ) → 𝐗 B ∈ Δ → Γ ⊢ Δ
  close (by decide) : Γ ⊢ Δ        -- when Γ and Δ share a formula
  topR    : ⊤ₗ ∈ Δ → Γ ⊢ Δ
  orL     : (A ⋎ B) ∈ Γ → A :: Γ ⊢ Δ → B :: Γ ⊢ Δ → Γ ⊢ Δ
  orR     : (A ⋎ B) ∈ Δ → Γ ⊢ A :: B :: Δ → Γ ⊢ Δ
  evL I   : (𝐅 A) ∈ Γ → [A] ⊢ [I] → [𝐗 I] ⊢ [I] → I :: Γ ⊢ Δ → Γ ⊢ Δ
  evR     : (𝐅 A) ∈ Δ → Γ ⊢ A :: 𝐗 (𝐅 A) :: Δ → Γ ⊢ Δ
"

/-- The prompt for proving `S ⊨ φ`. `atom` and `state` name atoms and states as
Lean terms; `sys` and `spec` are the Lean names of `S` and `φ`; `fType` is the
Lean type of formulas over the extended alphabet, e.g. `Formula (P ⊕ St)`. -/
def prompt (atom : AP → String) (state : Q → String) (sys spec fType : String)
    (φ : Formula AP) : String :=
  let ext : AP ⊕ Q → String
    | .inl p => s!"ap {atom p}"
    | .inr q => s!"at_ {state q}"
  let hyps := S.hyps.map (Formula.toLean ext)
  let numbered := (List.range hyps.length).zip hyps |>.map fun (i, h) => s!"  H{i} : {h}"
  let goal := (lift (Q := Q) φ).toLean ext
  let showList := "[" ++ ", ".intercalate hyps ++ "]"
  s!"You are writing a machine-checked proof in Lean 4, using a sequent calculus for LTL.

## Problem

Prove that every execution of the transition system `{sys}` satisfies the LTL
formula `{spec}` = {φ.toLean atom}.

System:
  states:  {", ".intercalate (S.states.map state)}
  initial: {", ".intercalate (S.init.map state)}
" ++ String.join (S.states.map fun q =>
    s!"  {state q} → [{", ".intercalate ((S.succ q).map state)}], labels [{", ".intercalate ((S.label q).map atom)}]\n") ++
s!"
The system is encoded as hypotheses, using the atom `at_ q` for \"in state q\" and
`ap p` for atom p:
{"\n".intercalate numbered}

It suffices to prove the sequent

  {sys}.hyps ⊢ [{goal}]

## Rules
{rulesText}
## How to write the proof

1. Start with
     show {showList} ⊢ [{goal}]
   and then `exact <term>`.
2. Give implicit arguments explicitly, e.g. `.alwaysL (A := at_ q1 ⇒ ap done) (by simp)`.
3. Discharge membership side conditions with `(by simp)` and close leaves with
   `.close (by decide)`.
4. The creative step is the invariant `I` in `alwaysR` (and `evL`, `untilL`).
   `alwaysR I` leaves three obligations: I holds now (Γ ⊢ I :: Δ), one step
   preserves it ([I] ⊢ [𝐗 I]), and it implies the goal ([I] ⊢ [A]). Since the
   last two have no context, put into I every hypothesis they need
   (for example the `𝐆 (at_ q ⇒ ...)` facts about the states I allows).
5. To reason about the next position, unfold `𝐆` hypotheses with `alwaysL`,
   then use `Derives.step` to move to the next position.

## Answer format

Reply with one Lean code block of this form:

abbrev I : {fType} := ...      -- optional: invariants and repeated formulas

theorem candidate : {sys}.hyps ⊢ [lift {spec}] := by
  show ...
  exact ...

Name formulas with `abbrev` before the theorem (with the type annotation), not
with `let` inside the proof: `simp` cannot see through `let`. Do not use
`sorry`. If you receive Lean error messages, fix the proof and reply with the
whole corrected block.
"

end System

end LTL
