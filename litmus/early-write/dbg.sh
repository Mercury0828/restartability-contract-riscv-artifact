#!/bin/bash
ISLA=${ISLA:-/root/restartv/isla/target/release/isla-axiomatic}
IR=${ISLA_IR:-/root/restartv/isla-snapshots-regen/rv64d_g58.ir}
CFG=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}/litmus/trap-scoping/riscv64_g2_trap_umode_ipo.toml
CAT=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}/litmus/cat/riscv_s1v2_nodrain.cat
"$ISLA" -A "$IR" -C "$CFG" --footprint-config "$CFG" -m "$CAT" -s 2400 -T "${2:-16}" "$1" > "dbg_$(basename $1 .toml).log" 2>&1
