#!/bin/bash
# z3_each.sh - run z3 on each saved isla candidate of one test (inside the 22.04 chroot) and record
# sat/unsat/unknown with seconds, to find the candidate behind an isla `error`.
# Usage (inside chroot): bash z3_each.sh <prefix> <outfile>
P="$1"; OUT="$2"
ls /tmp/${P}_*.smt2 | xargs -P 8 -I{} bash -c 'S=$(date +%s); R=$(timeout 2400 z3 {} 2>&1 | head -1); echo "$(basename {}) $R $(( $(date +%s)-S ))s"' > "$OUT"
