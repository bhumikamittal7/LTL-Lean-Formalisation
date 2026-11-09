#!/usr/bin/env python3
"""Run the propose-check loop on the benchmark problems.

For each problem, the proposer (a language model, called through its
CLI with all tools disabled, from an empty directory) receives the prompt
printed by `proposer/BenchPrompts.lean`. Its answer is placed in a candidate
file that ends with

    theorem verified : <Sys>.S.Models <Sys>.<spec> := <Sys>.S.sat_of_derives Candidate.candidate
    #print axioms verified

and Lean checks the file. If Lean reports errors, the prompt, the previous
answer, and the error messages go back to the proposer, up to MAX_ATTEMPTS
times. A proof counts as accepted only if Lean reports no errors and `verified`
depends on no axioms beyond Lean's standard ones (so no `sorry`).

Usage (from the repository root):
    python3 proposer/run_bench.py [--model MODEL] [--attempts N] [--jobs J] [--only Sys/spec ...]
Results go to runs/<timestamp>/.
"""

import argparse
import concurrent.futures as cf
import datetime as dt
import json
import pathlib
import re
import subprocess
import tempfile
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SYSTEM_PROMPT = (
    "You are an expert in Lean 4 and linear temporal logic. "
    "Follow the instructions in the user message and answer with one Lean code block."
)
LEAN_TIMEOUT = 600
MODEL_TIMEOUT = 900
MAX_ERROR_CHARS = 6000


def load_prompts():
    out = subprocess.run(
        ["lake", "env", "lean", "proposer/BenchPrompts.lean"],
        cwd=ROOT, capture_output=True, text=True, check=True,
    ).stdout
    prompts = {}
    parts = re.split(r"^===== (\S+) =====\n", out, flags=re.M)
    for name, body in zip(parts[1::2], parts[2::2]):
        prompts[name] = body.strip() + "\n"
    return prompts


def call_model(message, model, workdir):
    cmd = [
        "claude", "-p", "--tools", "", "--safe-mode", "--strict-mcp-config",
        "--no-session-persistence", "--system-prompt", SYSTEM_PROMPT,
        "--output-format", "json",
    ]
    if model:
        cmd += ["--model", model]
    t0 = time.time()
    r = subprocess.run(cmd, input=message, cwd=workdir, capture_output=True,
                       text=True, timeout=MODEL_TIMEOUT)
    d = json.loads(r.stdout)
    return {
        "text": d.get("result") or "",
        "models": list((d.get("modelUsage") or {}).keys()),
        "cost_usd": d.get("total_cost_usd"),
        "usage": d.get("usage"),
        "seconds": round(time.time() - t0, 1),
        "is_error": d.get("is_error"),
    }


def extract_code(text):
    blocks = re.findall(r"```(?:lean4?|)\s*\n(.*?)```", text, flags=re.S)
    return blocks[-1] if blocks else None


def candidate_file(sys_name, spec, code):
    ns = f"Bench.{sys_name}"
    return f"""import Bench

open LTL LTL.System
open {ns}
open {ns}.P {ns}.St

namespace Candidate

{code.strip()}

end Candidate

theorem verified : {ns}.S.Models {ns}.{spec} :=
  {ns}.S.sat_of_derives Candidate.candidate

#print axioms verified
"""


def check(path):
    t0 = time.time()
    try:
        r = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                           capture_output=True, text=True, timeout=LEAN_TIMEOUT)
        out = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return False, f"Lean timed out after {LEAN_TIMEOUT} s.", round(time.time() - t0, 1)
    secs = round(time.time() - t0, 1)
    errors = [l for l in out.splitlines() if ": error" in l]
    m = re.search(r"'verified' depends on axioms: \[(.*?)\]", out, flags=re.S)
    axioms = {a.strip() for a in m.group(1).split(",")} if m else None
    no_axioms = "'verified' does not depend on any axioms" in out
    ok = (not errors) and r.returncode == 0 and (no_axioms or (axioms is not None and axioms <= STD_AXIOMS))
    if ok:
        return True, out, secs
    if not errors and not ok:
        out += "\n(The proof was not accepted: `verified` must type-check and must not depend on `sorry` or extra axioms.)"
    return False, out, secs


def feedback(prompt, answer, errors):
    errors = errors.replace(str(ROOT) + "/", "")
    if len(errors) > MAX_ERROR_CHARS:
        errors = errors[:MAX_ERROR_CHARS] + "\n... (truncated)"
    return (
        prompt
        + "\n## Your previous answer\n\n```lean\n" + answer.strip() + "\n```\n"
        + "\n## Lean's response\n\nLean rejected the previous answer with these messages "
        + "(line numbers refer to a file in which your block starts at line 9):\n\n```\n"
        + errors.strip() + "\n```\n\nFix the proof and reply with the whole corrected block.\n"
    )


def run_problem(name, prompt, args, outdir):
    sys_name, spec = name.split("/")
    pdir = outdir / name.replace("/", "_")
    pdir.mkdir(parents=True, exist_ok=True)
    (pdir / "prompt.txt").write_text(prompt)
    log = {"problem": name, "attempts": [], "accepted": False}
    message = prompt
    with tempfile.TemporaryDirectory() as empty:
        for k in range(1, args.attempts + 1):
            att = {"attempt": k}
            try:
                resp = call_model(message, args.model, empty)
            except Exception as e:  # model call failed
                att["model_error"] = repr(e)
                log["attempts"].append(att)
                break
            att.update({key: resp[key] for key in ("models", "cost_usd", "usage", "seconds", "is_error")})
            (pdir / f"answer{k}.md").write_text(resp["text"])
            code = extract_code(resp["text"])
            if code is None:
                att["result"] = "no code block"
                log["attempts"].append(att)
                message = feedback(prompt, resp["text"], "Your answer contained no Lean code block.")
                continue
            path = pdir / f"Candidate{k}.lean"
            path.write_text(candidate_file(sys_name, spec, code))
            ok, out, secs = check(path)
            att["lean_seconds"] = secs
            (pdir / f"lean{k}.txt").write_text(out)
            att["result"] = "accepted" if ok else "rejected"
            log["attempts"].append(att)
            if ok:
                log["accepted"] = True
                break
            message = feedback(prompt, code, out)
    log["num_attempts"] = len(log["attempts"])
    (pdir / "log.json").write_text(json.dumps(log, indent=2))
    print(f"{name}: {'ACCEPTED' if log['accepted'] else 'failed'} after {log['num_attempts']} attempt(s)", flush=True)
    return log


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default=None)
    ap.add_argument("--attempts", type=int, default=5)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--only", nargs="*")
    args = ap.parse_args()
    prompts = load_prompts()
    names = args.only or list(prompts)
    stamp = dt.datetime.now().strftime("%Y%m%d-%H%M%S")
    outdir = ROOT / "runs" / stamp
    outdir.mkdir(parents=True)
    with cf.ThreadPoolExecutor(args.jobs) as ex:
        logs = list(ex.map(lambda n: run_problem(n, prompts[n], args, outdir), names))
    summary = {"model_arg": args.model, "max_attempts": args.attempts, "problems": logs}
    (outdir / "summary.json").write_text(json.dumps(summary, indent=2))
    print(f"\n{sum(l['accepted'] for l in logs)}/{len(logs)} accepted. Results in {outdir}")


if __name__ == "__main__":
    main()
