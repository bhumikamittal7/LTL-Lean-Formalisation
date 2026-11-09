# Benchmark results

All derivations here were written by the language model, with all tools
disabled and from an empty directory, and accepted by Lean. Each file is the candidate exactly as Lean checked it; it ends
with `#print axioms verified`. To re-check one, from the repository root:

    lake env lean bench-results/laws/law057.lean

* `laws/`: the 172 laws of Warford, Vega, and Staley, "A Calculational
  Deductive System for Linear Temporal Logic" (ACM Computing Surveys 53(3),
  2020) that use only next, always, eventually, until, and propositional
  connectives (statements in `proposer/laws.json`; runner
  `proposer/run_laws.py`). Each law is derived for arbitrary formulas
  `p q r : Formula AP`. All 172 accepted, 166 at the first attempt.
* `systems/`: `S ⊨ φ` problems (systems in `Bench/`; runner
  `proposer/run_bench.py`): the running example, the robot, and three systems
  from Baier and Katoen, *Principles of Model Checking* (vending machine,
  semaphore mutual exclusion, Peterson's algorithm). All 14 accepted.

`summary.json` in each folder records the attempts and the result of each.
