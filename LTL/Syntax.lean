/-!
# LTL syntax

Primitive connectives: `⊥ ¬ ∧ →` and the temporal operators `X` (next),
`G` (always), `U` (until). Disjunction, `⊤`, and `F` (eventually) are
abbreviations, so the proof system needs rules only for the primitives.
-/

namespace LTL

inductive Formula (AP : Type) where
  | atom : AP → Formula AP
  | bot : Formula AP
  | neg : Formula AP → Formula AP
  | and : Formula AP → Formula AP → Formula AP
  | imp : Formula AP → Formula AP → Formula AP
  | next : Formula AP → Formula AP
  | always : Formula AP → Formula AP
  | until : Formula AP → Formula AP → Formula AP
  deriving DecidableEq, Repr

namespace Formula

variable {AP AP' : Type}

/-- `⊤ := ¬⊥` -/
def top : Formula AP := neg bot
/-- `A ∨ B := ¬A → B` -/
def or (φ ψ : Formula AP) : Formula AP := imp (neg φ) ψ
/-- `F A := ⊤ U A` -/
def eventually (φ : Formula AP) : Formula AP := .until top φ

/-- Rename atoms. Used to move a specification into the alphabet of a system encoding. -/
def map (f : AP → AP') : Formula AP → Formula AP'
  | atom p => atom (f p)
  | bot => bot
  | neg φ => neg (map f φ)
  | and φ ψ => and (map f φ) (map f ψ)
  | imp φ ψ => imp (map f φ) (map f ψ)
  | next φ => next (map f φ)
  | always φ => always (map f φ)
  | .until φ ψ => .until (map f φ) (map f ψ)

/-- Finite disjunction; the empty disjunction is `⊥`. -/
def bigOr : List (Formula AP) → Formula AP
  | [] => bot
  | φ :: φs => or φ (bigOr φs)

end Formula

/-! ## Notation -/

scoped notation "⊥ₗ" => Formula.bot
scoped notation "⊤ₗ" => Formula.top
scoped infixr:25 " ⇒ " => Formula.imp
scoped infixr:30 " ⋎ " => Formula.or
scoped infixr:35 " ⋏ " => Formula.and
scoped notation:max "∼" φ:max => Formula.neg φ
scoped notation:max "𝐗" φ:max => Formula.next φ
scoped notation:max "𝐆" φ:max => Formula.always φ
scoped notation:max "𝐅" φ:max => Formula.eventually φ
scoped infix:50 " 𝐔 " => Formula.until

end LTL
