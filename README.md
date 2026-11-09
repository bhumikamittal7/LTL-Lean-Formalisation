# LTL Lean Formalisation

Given a finite transition system `S` and an LTL formula `φ`, a language model writes a derivation of `Γ_S ⊢ φ` in a sequent calculus for LTL, where `Γ_S` lists the facts about `S` as formulas. Lean checks the derivation and turns it into the theorem `S.Models φ`: every infinite execution of `S` satisfies `φ`. The model is never trusted; Lean rejects a wrong derivation and its error messages go back to the model.

The development uses only Lean's core library and contains no `sorry`. It includes 186 problems with every derivation the model wrote: 172 laws from a published catalogue of LTL theorems and 14 properties of 5 systems.


## Try it

Install [elan](https://github.com/leanprover/elan); it fetches the Lean version in `lean-toolchain` on the first build.

    lake build LTL Bench

Check a derivation written by the model, here for a robot that never enters its hazard cell:

    lake env lean bench-results/systems/Robot_specSafe.lean

Lean prints `'verified' depends on axioms: [propext, Classical.choice, Quot.sound]`, so the theorem `S.Models specSafe` holds and uses no `sorry`. The model's invariant is `Inv` in that file.

Print the prompt the model gets for the running example:

    lake env lean proposer/Prompt.lean


## Reproduce the results

| Command | What it does | Time |
|---|---|---|
| `./check_results.sh` | Re-checks all 186 derivations in `bench-results/` with Lean | 20 s |
| `python3 proposer/run_laws.py` | Runs the propose-check loop on the 172 laws | ~20 min |
| `python3 proposer/run_bench.py` | Runs the loop on the 14 system properties | ~15 min |

`./check_results.sh` ends with `186 of 186 derivations accepted`. The two loops call the model through the `claude` CLI with all tools disabled; they take `--model`, `--attempts` (default 5), `--jobs`, and `--only`, and write to `runs/`. `bench-results/` holds one full run: all 186 accepted, 175 at the first attempt. Times are from an Apple M5.


## Read the code

A result `S.Models φ` depends only on Lean's kernel and about 40 lines of definitions: `Formula` (`LTL/Syntax.lean`), `Trace` and `Sat` (`LTL/Semantics.lean`), and `System`, `IsExec`, `traceOf`, `Models` (`LTL/System.lean`). The two theorems that give an accepted derivation its meaning are

```lean
theorem soundness (h : Γ ⊢ Δ) : SValid Γ Δ                          -- LTL/Soundness.lean
theorem System.sat_of_derives (h : S.hyps ⊢ [lift φ]) : S.Models φ  -- LTL/System.lean
```

| Path | Contents |
|---|---|
| `LTL/Syntax.lean`, `LTL/Semantics.lean` | formulas and satisfaction at a position |
| `LTL/Sequent.lean` | the sequent calculus `Derives`, written `Γ ⊢ Δ` |
| `LTL/Soundness.lean` | every derivable sequent is valid |
| `LTL/Derived.lean` | weakening and rules for `⊤ ∨ F` |
| `LTL/System.lean` | transition systems, the hypotheses `Γ_S`, `sat_of_derives` |
| `LTL/Example.lean` | the running example, `S ⊨ F G done`, derived by hand |
| `LTL/Prompt.lean` | turns `S` and `φ` into a prompt |
| `Bench/` | the benchmark systems and their specifications |
| `proposer/` | the propose-check loops and the 172 law statements |
| `bench-results/` | every derivation the model wrote and Lean accepted |

Most rules take the goal apart one connective at a time, so the conclusion determines the premises. The exceptions are `cut` and the invariant rules `alwaysR` and `untilL`, which need a formula `I` that is not in the goal; finding `I` is the model's job.


## Add a system

Copy `Bench/Robot.lean`: define the atoms, the states, the system `S`, and its specifications. Import the file in `Bench.lean`, add an `emit` line per specification to `proposer/BenchPrompts.lean`, and run

    python3 proposer/run_bench.py --only MySystem/mySpec

Without that CLI, follow `proposer/README.md` to use any chat model by hand.


## Limits

Only infinite executions count: a system whose runs all deadlock satisfies every formula, so check that every state has a successor. Soundness is mechanized; completeness is not. A failed proof does not show that a property is false. Proofs grow with `Γ_S`, because the model writes out every rule application (262 lines for Peterson's algorithm).
