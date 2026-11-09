import Bench.Common

/-!
Semaphore-based mutual exclusion (Baier and Katoen, *Principles of Model
Checking*, Ch. 2). A state `xyk` gives the location of process 1 and process 2
(`n` noncritical, `w` waiting, `c` critical) and the semaphore value `k`. The
system has all 18 states of the program graph, reachable or not.
-/

namespace Bench.Semaphore
open LTL LTL.System

inductive P where
  | crit1 | crit2
  deriving DecidableEq, Repr

inductive St where
  | nn0
  | nn1
  | nw0
  | nw1
  | nc0
  | nc1
  | wn0
  | wn1
  | ww0
  | ww1
  | wc0
  | wc1
  | cn0
  | cn1
  | cw0
  | cw1
  | cc0
  | cc1
  deriving DecidableEq, Repr

open P St

def S : System P St where
  props := [crit1, crit2]
  states := [nn0, nn1, nw0, nw1, nc0, nc1, wn0, wn1, ww0, ww1, wc0, wc1, cn0, cn1, cw0, cw1, cc0, cc1]
  init := [nn1]
  succ
    | nn0 => [wn0, nw0]
    | nn1 => [wn1, nw1]
    | nw0 => [ww0]
    | nw1 => [ww1, nc0]
    | nc0 => [wc0, nn1]
    | nc1 => [wc1, nn1]
    | wn0 => [ww0]
    | wn1 => [cn0, ww1]
    | ww0 => [ww0]
    | ww1 => [cw0, wc0]
    | wc0 => [wn1]
    | wc1 => [cc0, wn1]
    | cn0 => [nn1, cw0]
    | cn1 => [nn1, cw1]
    | cw0 => [nw1]
    | cw1 => [nw1, cc0]
    | cc0 => [nc1, cn1]
    | cc1 => [nc1, cn1]
  label
    | nn0 => []
    | nn1 => []
    | nw0 => []
    | nw1 => []
    | nc0 => [crit2]
    | nc1 => [crit2]
    | wn0 => []
    | wn1 => []
    | ww0 => []
    | ww1 => []
    | wc0 => [crit2]
    | wc1 => [crit2]
    | cn0 => [crit1]
    | cn1 => [crit1]
    | cw0 => [crit1]
    | cw1 => [crit1]
    | cc0 => [crit1, crit2]
    | cc1 => [crit1, crit2]

/-- Never both critical. -/
def specMutex : Formula P := 𝐆 (∼((.atom crit1) ⋏ (.atom crit2)))

/-- Process 2 never enters right after process 1 was critical. -/
def specNoHandover : Formula P := 𝐆 ((.atom crit1) ⇒ 𝐗 (∼(.atom crit2)))

def atomName : P → String
  | crit1 => "crit1"
  | crit2 => "crit2"

def stateName : St → String
  | nn0 => "nn0"
  | nn1 => "nn1"
  | nw0 => "nw0"
  | nw1 => "nw1"
  | nc0 => "nc0"
  | nc1 => "nc1"
  | wn0 => "wn0"
  | wn1 => "wn1"
  | ww0 => "ww0"
  | ww1 => "ww1"
  | wc0 => "wc0"
  | wc1 => "wc1"
  | cn0 => "cn0"
  | cn1 => "cn1"
  | cw0 => "cw0"
  | cw1 => "cw1"
  | cc0 => "cc0"
  | cc1 => "cc1"

end Bench.Semaphore
