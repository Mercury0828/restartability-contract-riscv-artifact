#!/bin/bash
# run_all.sh - runs every frozen-suite test, 6 at a time, appending verbatim verdicts to
# /root/frozen_results.txt. Each isla invocation gets -T 4, so 6 x 4 = 24 of 32 cores.
set -u
D=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}/litmus/frozen-suite
R=/root/run_frozen_suite.sh
cp "$D/run_frozen_suite.sh" "$R"
sed -i 's/\r$//' "$R"
rm -f /root/frozen_results.txt
ls "$D"/FT*.toml | xargs -n 1 -P 6 -I{} bash "$R" /root/frozen_results.txt {}
echo DONE
