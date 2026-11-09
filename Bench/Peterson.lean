import Bench.Common

/-!
Peterson's mutual-exclusion algorithm (Baier and Katoen, *Principles of Model
Checking*, Ch. 2). A state `xyk` gives the locations of the two processes
(`n`, `w`, `c`) and the value `k` of the shared variable `turn`; the flags are
determined by the locations. The system has all 18 states, reachable or not.
-/

namespace Bench.Peterson
open LTL LTL.System

inductive P where
  | crit1 | crit2
  deriving DecidableEq, Repr

inductive St where
  | nn1
  | nn2
  | nw1
  | nw2
  | nc1
  | nc2
  | wn1
  | wn2
  | ww1
  | ww2
  | wc1
  | wc2
  | cn1
  | cn2
  | cw1
  | cw2
  | cc1
  | cc2
  deriving DecidableEq, Repr

open P St

def S : System P St where
  props := [crit1, crit2]
  states := [nn1, nn2, nw1, nw2, nc1, nc2, wn1, wn2, ww1, ww2, wc1, wc2, cn1, cn2, cw1, cw2, cc1, cc2]
  init := [nn1, nn2]
  succ
    | nn1 => [wn2, nw1]
    | nn2 => [wn2, nw1]
    | nw1 => [ww2, nc1]
    | nw2 => [ww2, nc2]
    | nc1 => [wc2, nn1]
    | nc2 => [wc2, nn2]
    | wn1 => [cn1, ww1]
    | wn2 => [cn2, ww1]
    | ww1 => [cw1]
    | ww2 => [wc2]
    | wc1 => [cc1, wn1]
    | wc2 => [wn2]
    | cn1 => [nn1, cw1]
    | cn2 => [nn2, cw1]
    | cw1 => [nw1]
    | cw2 => [nw2, cc2]
    | cc1 => [nc1, cn1]
    | cc2 => [nc2, cn2]
  label
    | nn1 => []
    | nn2 => []
    | nw1 => []
    | nw2 => []
    | nc1 => [crit2]
    | nc2 => [crit2]
    | wn1 => []
    | wn2 => []
    | ww1 => []
    | ww2 => []
    | wc1 => [crit2]
    | wc2 => [crit2]
    | cn1 => [crit1]
    | cn2 => [crit1]
    | cw1 => [crit1]
    | cw2 => [crit1]
    | cc1 => [crit1, crit2]
    | cc2 => [crit1, crit2]

/-- Never both critical. -/
def specMutex : Formula P := 𝐆 (∼((.atom crit1) ⋏ (.atom crit2)))

def atomName : P → String
  | crit1 => "crit1"
  | crit2 => "crit2"

def stateName : St → String
  | nn1 => "nn1"
  | nn2 => "nn2"
  | nw1 => "nw1"
  | nw2 => "nw2"
  | nc1 => "nc1"
  | nc2 => "nc2"
  | wn1 => "wn1"
  | wn2 => "wn2"
  | ww1 => "ww1"
  | ww2 => "ww2"
  | wc1 => "wc1"
  | wc2 => "wc2"
  | cn1 => "cn1"
  | cn2 => "cn2"
  | cw1 => "cw1"
  | cw2 => "cw2"
  | cc1 => "cc1"
  | cc2 => "cc2"

end Bench.Peterson
