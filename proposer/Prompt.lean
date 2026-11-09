import LTL

/-!
Print the proposer prompt for the running example:

    lake env lean proposer/Prompt.lean

To use another system, define it like `LTL.Example.S` and change the call below.
-/

open LTL LTL.Example

def atomName : P → String
  | .wait => "wait"
  | .done => "done"

def stateName : St → String
  | .q0 => "q0"
  | .q1 => "q1"

#eval IO.println (S.prompt atomName stateName "S" "spec" "Formula (P ⊕ St)" spec)
