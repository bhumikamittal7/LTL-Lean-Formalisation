#!/usr/bin/env python3
"""Run the propose-check loop on the LTL laws of `proposer/laws.json`.

Each law must be derived in the sequent calculus for arbitrary formulas
`p q r : Formula AP`. The proposer, the checking, and the feedback are the same
as in `run_bench.py`; only the prompt and the candidate file differ.

Usage (from the repository root):
    python3 proposer/run_laws.py [--model M] [--attempts N] [--jobs J] [--only 1 23 ...]
    python3 proposer/run_laws.py --typecheck    # elaborate every goal with `sorry`
Results go to runs/laws-<timestamp>/.
"""

import argparse
import concurrent.futures as cf
import datetime as dt
import json
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parent))
import laws as L  # noqa: E402
from run_bench import ROOT, call_model, extract_code, check, feedback  # noqa: E402


def rules_text():
    src = (ROOT / "LTL" / "Prompt.lean").read_text()
    return re.search(r'def rulesText : String := "\n(.*?)\n"', src, re.S).group(1)


def signature(law):
    vs = " ".join(law["vars"])
    binders = f" ({vs} : Formula AP)" if vs else ""
    return f"theorem candidate {{AP : Type}}{binders} :\n    {law['lean_goal']}"


def prompt(law):
    kind = ("an equivalence: prove both directions as a pair `⟨_, _⟩`"
            if "≈" in law["statement"] else "an entailment")
    return f"""You are writing a machine-checked proof in Lean 4, using a sequent calculus for LTL.

## Problem

Prove the LTL law

    {law['statement']}

where ◯ is next, □ always, ◇ eventually, U until, `A ⟹ B` means that every
trace satisfying A satisfies B, and `A ≈ B` means both directions. The law is
{kind}. It must hold for arbitrary formulas, so prove

{signature(law)}

## Rules
{rules_text()}
## How to write the proof

1. `p`, `q`, `r` are arbitrary formulas, not atoms. Close a leaf with
   `.ax (A := X) (by simp) (by simp)` when X is on both sides, or with
   `.botL (by simp)`. (`Derives.close` needs decidable equality and does not
   apply here.)
2. Give implicit arguments explicitly, e.g. `.alwaysL (A := p) (by simp) ...`.
3. Discharge membership side conditions with `(by simp)`.
4. The creative step is the invariant `I` in `alwaysR`, `untilL`, and `evL`.
   `alwaysR I` leaves three obligations: I holds now (Γ ⊢ I :: Δ), one step
   preserves it ([I] ⊢ [𝐗 I]), and it implies the goal ([I] ⊢ [A]). The last two
   have no context, so put into I everything they need.
5. To reason about the next position, unfold `𝐆` with `alwaysL`, `𝐔` with
   `untilR`, `𝐅` with `evR`, and then move to the next position with
   `Derives.step` or `Derives.next`.

## Answer format

Reply with one Lean code block that contains `theorem candidate` with exactly
the statement above. You may put helper theorems (with other names) and
`abbrev`s before it. Do not use `sorry`. If you receive Lean error messages,
fix the proof and reply with the whole corrected block.
"""


def candidate_file(law, code):
    vs = " ".join(law["vars"])
    binders = f" ({vs} : Formula AP)" if vs else ""
    return f"""import LTL

open LTL

-- LTL law {law['number']}: {law['statement']}
-- (the proposer's answer starts at line 9)

namespace Candidate
{code.strip()}

end Candidate

theorem verified {{AP : Type}}{binders} :
    {law['lean_goal']} :=
  Candidate.candidate {vs}

#print axioms verified
"""


def typecheck(laws):
    body = ["import LTL", "open LTL", ""]
    for n, law in laws.items():
        vs = " ".join(law["vars"])
        binders = f" ({vs} : Formula AP)" if vs else ""
        body.append(f"example {{AP : Type}}{binders} : {law['lean_goal']} := sorry")
    path = ROOT / "runs" / "_laws_typecheck.lean"
    path.parent.mkdir(exist_ok=True)
    path.write_text("\n".join(body) + "\n")
    out = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                         capture_output=True, text=True)
    errs = [l for l in (out.stdout + out.stderr).splitlines() if ": error" in l]
    print(f"{len(laws)} goals elaborated, {len(errs)} errors")
    for e in errs[:20]:
        print(e)


def run_law(law, args, outdir):
    pdir = outdir / f"law{int(law['number']):03d}"
    pdir.mkdir(parents=True, exist_ok=True)
    first = prompt(law)
    (pdir / "prompt.txt").write_text(first)
    log = {"problem": f"law {law['number']}", "statement": law["statement"],
           "attempts": [], "accepted": False}
    message = first
    with tempfile.TemporaryDirectory() as empty:
        for k in range(1, args.attempts + 1):
            att = {"attempt": k}
            try:
                resp = call_model(message, args.model, empty)
            except Exception as e:
                att["model_error"] = repr(e)
                log["attempts"].append(att)
                break
            att.update({key: resp[key] for key in ("models", "usage", "is_error")})
            (pdir / f"answer{k}.md").write_text(resp["text"])
            code = extract_code(resp["text"])
            if code is None:
                att["result"] = "no code block"
                log["attempts"].append(att)
                message = feedback(first, resp["text"], "Your answer contained no Lean code block.")
                continue
            path = pdir / f"Candidate{k}.lean"
            path.write_text(candidate_file(law, code))
            ok, out, secs = check(path)
            (pdir / f"lean{k}.txt").write_text(out)
            att["result"] = "accepted" if ok else "rejected"
            log["attempts"].append(att)
            if ok:
                log["accepted"] = True
                break
            message = feedback(first, code, out)
    log["num_attempts"] = len(log["attempts"])
    (pdir / "log.json").write_text(json.dumps(log, indent=2, ensure_ascii=False))
    print(f"law {law['number']}: {'ACCEPTED' if log['accepted'] else 'failed'} "
          f"after {log['num_attempts']} attempt(s)", flush=True)
    return log


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default=None)
    ap.add_argument("--attempts", type=int, default=5)
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--typecheck", action="store_true")
    args = ap.parse_args()
    laws = L.load()
    for n, law in laws.items():
        law["number"] = n
    if args.only:
        laws = {n: laws[n] for n in args.only}
    if args.typecheck:
        typecheck(laws)
        return
    stamp = dt.datetime.now().strftime("%Y%m%d-%H%M%S")
    outdir = ROOT / "runs" / f"laws-{stamp}"
    outdir.mkdir(parents=True)
    with cf.ThreadPoolExecutor(args.jobs) as ex:
        logs = list(ex.map(lambda law: run_law(law, args, outdir), laws.values()))
    summary = {"model_arg": args.model, "max_attempts": args.attempts, "problems": logs}
    (outdir / "summary.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False))
    print(f"\n{sum(l['accepted'] for l in logs)}/{len(logs)} accepted. Results in {outdir}")


if __name__ == "__main__":
    main()
