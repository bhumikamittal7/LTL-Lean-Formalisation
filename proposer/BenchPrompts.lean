import Bench

/-!
Print the proposer prompt for every benchmark problem, separated by marker
lines `===== <System>/<spec> =====`. Used by `proposer/run_bench.py`.
-/

open LTL

def emit {AP Q : Type} [DecidableEq AP] (S : System AP Q) (sys : String)
    (atom : AP → String) (state : Q → String) (specName : String)
    (φ : Formula AP) : IO Unit := do
  IO.println s!"===== {sys}/{specName} ====="
  IO.println (S.prompt atom state "S" specName "Formula (P ⊕ St)" φ)

open Bench in
#eval do
  emit Wait.S "Wait" Wait.atomName Wait.stateName "specFG" Wait.specFG
  emit Wait.S "Wait" Wait.atomName Wait.stateName "specUntil" Wait.specUntil
  emit Wait.S "Wait" Wait.atomName Wait.stateName "specNext" Wait.specNext
  emit Robot.S "Robot" Robot.atomName Robot.stateName "specSafe" Robot.specSafe
  emit Robot.S "Robot" Robot.atomName Robot.stateName "specRecur" Robot.specRecur
  emit Robot.S "Robot" Robot.atomName Robot.stateName "specResp" Robot.specResp
  emit Robot.S "Robot" Robot.atomName Robot.stateName "specReach" Robot.specReach
  emit Vending.S "Vending" Vending.atomName Vending.stateName "specResp" Vending.specResp
  emit Vending.S "Vending" Vending.atomName Vending.stateName "specRecur" Vending.specRecur
  emit Vending.S "Vending" Vending.atomName Vending.stateName "specPrec" Vending.specPrec
  emit Vending.S "Vending" Vending.atomName Vending.stateName "specNext" Vending.specNext
  emit Semaphore.S "Semaphore" Semaphore.atomName Semaphore.stateName "specMutex" Semaphore.specMutex
  emit Semaphore.S "Semaphore" Semaphore.atomName Semaphore.stateName "specNoHandover" Semaphore.specNoHandover
  emit Peterson.S "Peterson" Peterson.atomName Peterson.stateName "specMutex" Peterson.specMutex
