# Manual proposer loop

This is the manual version of the propose-check loop, for any chat model.
`run_bench.py` and `run_laws.py` automate it.

1. Print the prompt for the verification problem:

       lake env lean proposer/Prompt.lean > prompt.txt

   (`Prompt.lean` sets up the running example; for another system, define it
   like `LTL.Example.S` and change the `#eval` line.)

2. Paste `prompt.txt` into an LLM.

3. Replace the `abbrev`s and `theorem candidate` in `proposer/Candidate.lean`
   with the answer. Keep the header (imports, `open`s, namespace) and the final
   `theorem verified`.

4. Check it:

       lake env lean proposer/Candidate.lean

   No output: Lean accepted the proof, and `verified : S.Models spec` holds.
   Errors: paste them back to the LLM and go to step 3.

`Candidate.lean` currently holds a reference answer for the running example.
