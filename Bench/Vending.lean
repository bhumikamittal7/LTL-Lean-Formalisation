import Bench.Common

/-!
The beverage vending machine of Baier and Katoen, *Principles of Model
Checking* (MIT Press, 2008), Example 2.2: after a coin is inserted, the machine
delivers soda or beer and returns to `pay`.
-/

namespace Bench.Vending
open LTL LTL.System

inductive P where
  | paid | drink
  deriving DecidableEq, Repr

inductive St where
  | pay
  | select
  | soda
  | beer
  deriving DecidableEq, Repr

open P St

def S : System P St where
  props := [paid, drink]
  states := [pay, select, soda, beer]
  init := [pay]
  succ
    | pay => [select]
    | select => [soda, beer]
    | soda => [pay]
    | beer => [pay]
  label
    | pay => []
    | select => [paid]
    | soda => [paid, drink]
    | beer => [paid, drink]

/-- Every payment is followed by a drink. -/
def specResp : Formula P := 𝐆 ((.atom paid) ⇒ 𝐅 (.atom drink))

/-- Drinks are delivered infinitely often. -/
def specRecur : Formula P := 𝐆 (𝐅 (.atom drink))

/-- No drink before payment. -/
def specPrec : Formula P := (∼(.atom drink)) 𝐔 (.atom paid)

/-- After a drink, the machine is unpaid again. -/
def specNext : Formula P := 𝐆 ((.atom drink) ⇒ 𝐗 (∼(.atom paid)))

def atomName : P → String
  | paid => "paid"
  | drink => "drink"

def stateName : St → String
  | pay => "pay"
  | select => "select"
  | soda => "soda"
  | beer => "beer"

end Bench.Vending
