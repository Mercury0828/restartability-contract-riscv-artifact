#!/bin/bash
# retry_errors.sh - re-runs, at LOW CONTENTION and with a larger SMT timeout, every frozen-suite
# test that came back `error` in the parallel pass.
#
# WHY: isla's `-s` is a per-SMT-call timeout in WALL-CLOCK seconds. Running six isla instances at
# -T 4 on a 32-core box inflates each z3 call, and a z3 timeout is reported by isla as `error`
# ("Error in parsing smt output to get allowed/forbidden", z3 head: 'timeout'). So the parallel
# pass can UNDER-report. The converse is not possible: contention can never turn a genuine
# `forbidden` into an `allowed` or vice versa, it can only prevent a verdict. Therefore
# parallel-pass VERDICTS stand as measured and only the `error`s are re-measured here.
#
# This pass: 2 concurrent, -T 8 (16 of 32 cores), -s 900 (3x the parallel pass's budget).
# Results -> /root/frozen_retry.txt, same <basename><TAB><verbatim line> format.
set -u
ISLA=${ISLA:-/root/restartv/isla/target/release/isla-axiomatic}
IR=${ISLA_IR:-/root/restartv/isla-snapshots-regen/rv64d_g58.ir}
CFG=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}/litmus/trap-scoping/riscv64_g2_trap_umode_ipo.toml
CAT=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}/litmus/cat/riscv_s1v2_nodrain.cat
D=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}/litmus/frozen-suite

one () {
  B="$1"
  T="$D/$B.toml"
  LOG=$(mktemp)
  timeout 5400 "$ISLA" -A "$IR" -C "$CFG" --footprint-config "$CFG" -m "$CAT" \
      -s 900 -T 8 "$T" > "$LOG" 2>&1
  RC=$?
  LINE=$(grep -aE "^$B (allowed|forbidden|error|timeout)" "$LOG" | tail -1 \
         | sed -e 's/\x1b\[[0-9;]*m//g' -e 's/ \.\{2,\}.*$//' -e 's/[[:space:]]*$//')
  if [ -z "$LINE" ]; then
    LINE="NO-SUMMARY-LINE rc=$RC last: $(grep -av 'No primop' "$LOG" | tail -2 | tr '\n' ' ')"
  fi
  printf '%s\t%s\n' "$B" "$LINE" >> /root/frozen_retry.txt
  rm -f "$LOG"
}

if [ "${1:-}" = "--one" ]; then one "$2"; exit 0; fi

rm -f /root/frozen_retry.txt
awk -F'\t' '$2 ~ / error /{print $1}' /root/frozen_results.txt \
  | xargs -n 1 -P 2 -I{} bash "$0" --one {}
echo RETRY_DONE
