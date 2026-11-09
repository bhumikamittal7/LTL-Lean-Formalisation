import Bench.Common

/-! The running example: a process waits for one step and is then done forever. -/

namespace Bench.Wait
open LTL LTL.System

inductive P where
  | wait | done
  deriving DecidableEq, Repr

inductive St where
  | q0 | q1
  deriving DecidableEq, Repr

open P St

def S : System P St where
  props := [wait, done]
  states := [q0, q1]
  init := [q0]
  succ
    | q0 => [q1]
    | q1 => [q1]
  label
    | q0 => [wait]
    | q1 => [done]

/-- From some point on, always done. -/
def specFG : Formula P := 𝐅 (𝐆 (.atom done))
/-- Wait until done. -/
def specUntil : Formula P := (.atom wait) 𝐔 (.atom done)
/-- Whenever waiting, done at the next step. -/
def specNext : Formula P := 𝐆 ((.atom wait) ⇒ 𝐗 (.atom done))

def atomName : P → String
  | wait => "wait" | done => "done"
def stateName : St → String
  | q0 => "q0" | q1 => "q1"

end Bench.Wait
