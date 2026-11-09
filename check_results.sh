#!/usr/bin/env bash
# Re-check every derivation in bench-results/ with Lean, without calling a language model.
# A file passes if Lean reports no errors and `verified` depends only on Lean's
# standard axioms (propext, Classical.choice, Quot.sound), so no `sorry`.
#
# Usage (from the repository root):  ./check_results.sh [JOBS]
set -u
cd "$(dirname "$0")"
jobs="${1:-8}"
lake build LTL Bench >/dev/null || { echo "lake build failed"; exit 1; }

check() {
  f="$1"
  out="$(lake env lean "$f" 2>&1)"
  if [ $? -ne 0 ]; then echo "FAIL $f (Lean error)"; return; fi
  if printf '%s\n' "$out" | grep -q "error"; then echo "FAIL $f (Lean error)"; return; fi
  line="$(printf '%s\n' "$out" | grep "depends on axioms")"
  if [ -z "$line" ]; then echo "FAIL $f (no axiom report)"; return; fi
  ax="$(printf '%s\n' "$line" | sed 's/.*\[\(.*\)\].*/\1/')"
  for a in $(printf '%s' "$ax" | tr ',' ' '); do
    case "$a" in propext|Classical.choice|Quot.sound) ;; *) echo "FAIL $f (axiom $a)"; return ;; esac
  done
  echo "ok   $f"
}
export -f check

files=(bench-results/laws/*.lean bench-results/systems/*.lean)
results="$(printf '%s\n' "${files[@]}" | xargs -P "$jobs" -I{} bash -c 'check "$@"' _ {})"
printf '%s\n' "$results" | grep -v '^ok' || true
ok="$(printf '%s\n' "$results" | grep -c '^ok')"
echo "$ok of ${#files[@]} derivations accepted"
[ "$ok" -eq "${#files[@]}" ]
