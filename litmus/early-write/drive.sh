#!/bin/bash
# drive.sh - run the early-write suite in three streams, detached.
cd ${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}/litmus/early-write
( bash run_ew.sh RESULTS_raw.txt 2400 8 EW_AF_r00.toml EW_AF_r06.toml ) &
( bash run_ew.sh RESULTS_raw.txt 2400 8 EW_AF_r50.toml EW_AF_r56.toml ) &
( bash run_ew.sh RESULTS_raw.txt 2400 12 EW_BF_r575.toml ) &
wait
echo DONE >> RESULTS_raw.txt
