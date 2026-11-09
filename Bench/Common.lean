import LTL

/-!
# Benchmark problems

Each problem is a finite transition system `S` and an LTL specification. The
proposer must derive `S.hyps ⊢ [lift spec]`; `System.sat_of_derives` then gives
`S.Models spec`. Every system lists its atoms and states with names that are
also Lean identifiers, so the prompt can refer to them directly.
-/
