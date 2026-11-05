#!/bin/bash
# run_ew.sh - runner for the early-write suite; same recipe as frozen-suite/run_frozen_suite.sh.
# Usage: bash run_ew.sh [-x <extra.smt2>] <outfile> <budget_s> <threads> <test.toml> [...]
# -x passes isla --extra-smt (SMT placed after the assertions, before check-sat).
# Records the verbatim isla-axiomatic summary line of each test, with its wall-clock seconds.
set -u
ISLA=${ISLA:-/root/restartv/isla/target/release/isla-axiomatic}
IR=${ISLA_IR:-/root/restartv/isla-snapshots-regen/rv64d_g58.ir}
CFG=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}/litmus/trap-scoping/riscv64_g2_trap_umode_ipo.toml
CAT=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}/litmus/cat/riscv_s1v2_nodrain.cat
XS=()
if [ "$1" = "-x" ]; then XS=(--extra-smt "$2"); shift 2; fi
OUT="$1"; BUD="$2"; THR="$3"; shift 3
for T in "$@"; do
  B=$(basename "$T" .toml)
  LOG=$(mktemp)
  S=$(date +%s)
  timeout $((BUD + 120)) "$ISLA" -A "$IR" -C "$CFG" --footprint-config "$CFG" -m "$CAT" \
      -s "$BUD" -T "$THR" "${XS[@]}" "$T" > "$LOG" 2>&1
  RC=$?
  E=$(( $(date +%s) - S ))
  LINE=$(grep -aE "^$B (allowed|forbidden|error|timeout)" "$LOG" | tail -1 \
         | sed -e 's/\x1b\[[0-9;]*m//g' -e 's/ \.\{2,\}.*$//' -e 's/[[:space:]]*$//')
  if [ -z "$LINE" ]; then
    LAST=$(grep -av 'No primop' "$LOG" | tail -2 | tr '\n' ' ')
    LINE="NO-SUMMARY-LINE rc=$RC last: $LAST"
  fi
  printf '%s\t%s\t%ss\n' "$B" "$LINE" "$E" >> "$OUT"
  rm -f "$LOG"
done
