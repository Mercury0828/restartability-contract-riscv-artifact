#!/bin/bash
# retry_final.sh - third and last attempt for the two frozen-suite tests that still returned
# `error` after the -s 900 low-contention pass. Whole machine, -s 2400.
# If a test still errors here it is reported as NOT DELIVERED, with its verbatim failure.
set -u
ISLA=${ISLA:-/root/restartv/isla/target/release/isla-axiomatic}
IR=${ISLA_IR:-/root/restartv/isla-snapshots-regen/rv64d_g58.ir}
CFG=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}/litmus/trap-scoping/riscv64_g2_trap_umode_ipo.toml
CAT=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}/litmus/cat/riscv_s1v2_nodrain.cat
D=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}/litmus/frozen-suite

go () {
  B="$1"
  LOG=/root/final_$B.log
  timeout 6000 "$ISLA" -A "$IR" -C "$CFG" --footprint-config "$CFG" -m "$CAT" \
      -s 2400 -T 14 "$D/$B.toml" > "$LOG" 2>&1
  RC=$?
  LINE=$(grep -aE "^$B (allowed|forbidden|error|timeout)" "$LOG" | tail -1 \
         | sed -e 's/\x1b\[[0-9;]*m//g' -e 's/ \.\{2,\}.*$//' -e 's/[[:space:]]*$//')
  [ -z "$LINE" ] && LINE="NO-SUMMARY-LINE rc=$RC last: $(grep -av 'No primop' "$LOG" | tail -2 | tr '\n' ' ')"
  printf '%s\t%s\n' "$B" "$LINE" >> /root/frozen_final.txt
}

rm -f /root/frozen_final.txt
go FT01_c_val2 &
go FT10_a_handler_store_after_csrw &
wait
echo FINAL_DONE
