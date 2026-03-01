#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 2 ]]; then
  cat <<'USAGE'
Usage:
  tools/logic_check.sh '<original_ltl>' '<simplified_ltl>'

Example:
  tools/logic_check.sh 'G(a) && G(b)' 'G(a && b)'
USAGE
  exit 2
fi

if ! command -v ltlfilt >/dev/null 2>&1; then
  echo "ERROR: 'ltlfilt' (Spot) is not installed or not in PATH." >&2
  echo "Install Spot first: https://spot.lre.epita.fr/" >&2
  exit 127
fi

orig="$1"
simp="$2"

count_eq=$(ltlfilt -c -f "$orig" --equivalent-to "$simp" || true)
count_orig_true=$(ltlfilt -c -f "$orig" --equivalent-to 'true' || true)
count_orig_false=$(ltlfilt -c -f "$orig" --equivalent-to 'false' || true)
count_simp_true=$(ltlfilt -c -f "$simp" --equivalent-to 'true' || true)
count_simp_false=$(ltlfilt -c -f "$simp" --equivalent-to 'false' || true)

echo "== Equivalence Check =="
if [[ "$count_eq" == "1" ]]; then
  echo "PASS: simplified formula is semantically equivalent to original."
else
  echo "FAIL: simplified formula is NOT equivalent to original."
fi

echo

echo "== Silent-Error Heuristics =="
if [[ "$count_orig_true" == "1" ]]; then
  echo "WARN: original formula is tautological (equivalent to true)."
fi
if [[ "$count_orig_false" == "1" ]]; then
  echo "WARN: original formula is inconsistent/unsatisfiable (equivalent to false)."
fi
if [[ "$count_simp_true" == "1" ]]; then
  echo "WARN: simplified formula is tautological (equivalent to true)."
fi
if [[ "$count_simp_false" == "1" ]]; then
  echo "WARN: simplified formula is inconsistent/unsatisfiable (equivalent to false)."
fi

if [[ "$count_orig_true" != "1" && "$count_orig_false" != "1" && "$count_simp_true" != "1" && "$count_simp_false" != "1" ]]; then
  echo "No tautology/unsat issue detected by basic checks."
fi

if [[ "$count_eq" != "1" ]]; then
  exit 1
fi
