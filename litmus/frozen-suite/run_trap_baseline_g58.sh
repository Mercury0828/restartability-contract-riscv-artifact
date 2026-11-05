#!/bin/bash
# run_trap_baseline_g58.sh - second attempt for the pre-existing trap-scoping tests that came back
# `error` on rv64d.ir, re-run on rv64d_g58.ir.
#
# Every one of those errors is the SAME footprint crash the rvwmo suite hits on rv64d.ir:
#   error: Symbolic (bit)vector length in subrange_internal
#   Backtrace: zisla_footprint / zisla_footprint_no_init / zexecute / zvmem_write
# It fires exactly when a store's ADDRESS is symbolic, which is why the three rv64d.ir tests that
# DO return verdicts (diag_umode_exit_fixed, trap_store_faultB1_defaults, trap_store_faultB2_replay)
# are precisely the three whose only memory accesses are to the CONCRETE address 0x84001000.
# rv64d_g58.ir carries model/split_misaligned_footprint_fix.patch and does not crash.
set -u
ISLA=${ISLA:-/root/restartv/isla/target/release/isla-axiomatic}
IR=${ISLA_IR:-/root/restartv/isla-snapshots-regen/rv64d_g58.ir}
REPO=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}
TS=$REPO/litmus/trap-scoping
CAT_STOCK=/root/restartv/isla/web/client/dist/riscv.cat
CFG_STOCK=/root/restartv/isla/configs/riscv64_g2.toml

go () {  # $1 test-basename  $2 config  $3 cat
  LOG=$(mktemp)
  timeout 2400 "$ISLA" -A "$IR" -C "$2" --footprint-config "$2" -m "$3" -s 300 -T 4 \
      "$TS/$1.toml" > "$LOG" 2>&1
  RC=$?
  LINE=$(grep -aE "^[A-Za-z0-9_.+-]+ (allowed|forbidden|error|timeout) " "$LOG" | tail -1 \
         | sed -e 's/\x1b\[[0-9;]*m//g' -e 's/ \.\{2,\}.*$//' -e 's/[[:space:]]*$//')
  [ -z "$LINE" ] && LINE="NO-SUMMARY-LINE rc=$RC last: $(grep -av 'No primop' "$LOG" | tail -2 | tr '\n' ' ')"
  printf '%s\t%s\n' "$1" "$LINE" >> /root/baseline_trap_g58.txt
  rm -f "$LOG"
}

rm -f /root/baseline_trap_g58.txt
go S1_mp                "$CFG_STOCK"                    "$REPO/litmus/cat/riscv_s1_nodrain.cat" &
go S1_control_fence     "$CFG_STOCK"                    "$REPO/litmus/cat/riscv_s1_nodrain.cat" &
go trap_ecall_working   "$TS/riscv64_g2_trap.toml"      "$CAT_STOCK" &
go trap_ecall           "$TS/riscv64_g2_trap.toml"      "$CAT_STOCK" &
go trap_store_faultA    "$TS/riscv64_g2_trap.toml"      "$CAT_STOCK" &
go trap_store_faultB1   "$TS/riscv64_g2_trap_umode.toml" "$CAT_STOCK" &
go diag_umode_exit      "$TS/riscv64_g2_trap_umode.toml" "$CAT_STOCK" &
wait
echo TRAP_G58_DONE
