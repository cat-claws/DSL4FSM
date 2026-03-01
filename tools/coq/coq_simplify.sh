#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  cat <<'USAGE'
Usage:
  tools/coq/coq_simplify.sh '<coq_list_term>'

Example:
  tools/coq/coq_simplify.sh '[Glob (Atom 1); Glob (LNot (Atom 2)); LTrue; Glob (Atom 1)]'
USAGE
  exit 2
fi

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
COQ_DIR="$ROOT/tools/coq"
TERM="$1"

# Compile kernel library (idempotent).
conda run -n rh1 coqc -Q "$COQ_DIR" DSL4FSM "$COQ_DIR/ltl_kernel.v" >/dev/null

TMP="/tmp/coqtmp$RANDOM$RANDOM.v"
cat > "$TMP" <<COQ
From Coq Require Import List.
Import ListNotations.
From DSL4FSM Require Import ltl_kernel.

Definition input_conj : list ltl := $TERM.

Eval vm_compute in (simplify_conj input_conj).
Eval vm_compute in (conj_to_ltl (simplify_conj input_conj)).
COQ

conda run -n rh1 coqc -Q "$COQ_DIR" DSL4FSM "$TMP"
rm -f "$TMP"
