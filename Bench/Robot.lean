import Bench.Common

/-!
A warehouse robot under a fixed policy. The map has four reachable cells and a
hazard cell that the policy never enters:

    cA → cB or cC,   cB → cC,   cC → cDock,   cDock → cA,   cHaz → cHaz

The robot starts in `cA`. Its battery is low in `cB`.
-/

namespace Bench.Robot
open LTL LTL.System

inductive P where
  | dock | hazard | low
  deriving DecidableEq, Repr

inductive St where
  | cA | cB | cC | cDock | cHaz
  deriving DecidableEq, Repr

open P St

def S : System P St where
  props := [dock, hazard, low]
  states := [cA, cB, cC, cDock, cHaz]
  init := [cA]
  succ
    | cA => [cB, cC]
    | cB => [cC]
    | cC => [cDock]
    | cDock => [cA]
    | cHaz => [cHaz]
  label
    | cA => []
    | cB => [low]
    | cC => []
    | cDock => [dock]
    | cHaz => [hazard]

/-- Never in the hazard cell. -/
def specSafe : Formula P := 𝐆 (∼(.atom hazard))
/-- At the dock infinitely often. -/
def specRecur : Formula P := 𝐆 (𝐅 (.atom dock))
/-- Whenever the battery is low, the robot eventually docks. -/
def specResp : Formula P := 𝐆 ((.atom low) ⇒ 𝐅 (.atom dock))
/-- The robot avoids the hazard until it reaches the dock. -/
def specReach : Formula P := (∼(.atom hazard)) 𝐔 (.atom dock)

def atomName : P → String
  | dock => "dock" | hazard => "hazard" | low => "low"
def stateName : St → String
  | cA => "cA" | cB => "cB" | cC => "cC" | cDock => "cDock" | cHaz => "cHaz"

end Bench.Robot
