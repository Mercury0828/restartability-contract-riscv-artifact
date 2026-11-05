#!/bin/bash
# run_frozen_suite.sh - runner for the RESTART-V frozen litmus suite (deliverable D-c).
#
# Usage:  bash run_frozen_suite.sh <outfile> <test.toml> [<test.toml> ...]
#
# Records the VERBATIM isla-axiomatic summary line for each test, one per line, as
#     <basename><TAB><verbatim summary line>
# Nothing is interpreted or normalised: `error`, `forbidden`, `timeout` and `allowed` are recorded
# exactly as isla printed them. If isla produced no summary line at all, the literal token
# NO-SUMMARY-LINE is recorded together with the last stderr line, and the test is NOT a delivered
# test.
set -u

ISLA=${ISLA:-/root/restartv/isla/target/release/isla-axiomatic}
IR=${ISLA_IR:-/root/restartv/isla-snapshots-regen/rv64d_g58.ir}
CFG=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}/litmus/trap-scoping/riscv64_g2_trap_umode_ipo.toml
CAT=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}/litmus/cat/riscv_s1v2_nodrain.cat

OUT="$1"; shift

for T in "$@"; do
  B=$(basename "$T" .toml)
  LOG=$(mktemp)
  timeout 2400 "$ISLA" -A "$IR" -C "$CFG" --footprint-config "$CFG" -m "$CAT" \
      -s 300 -T 4 "$T" > "$LOG" 2>&1
  RC=$?
  # The summary line is the one naming the test followed by a verdict word.
  LINE=$(grep -aE "^$B (allowed|forbidden|error|timeout)" "$LOG" | tail -1 \
         | sed -e 's/\x1b\[[0-9;]*m//g' -e 's/ \.\{2,\}.*$//' -e 's/[[:space:]]*$//')
  if [ -z "$LINE" ]; then
    LAST=$(grep -av 'No primop' "$LOG" | tail -2 | tr '\n' ' ')
    LINE="NO-SUMMARY-LINE rc=$RC last: $LAST"
  fi
  printf '%s\t%s\n' "$B" "$LINE" >> "$OUT"
  rm -f "$LOG"
done
