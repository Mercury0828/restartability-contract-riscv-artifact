#!/bin/bash
# z3_variants.sh - re-solve the one BF candidate z3 left `unknown` under other z3 settings (inside chroot)
F=/tmp/isla_candidate_EWBFrfive7five_g0t0_752836_10.smt2
run () { S=$(date +%s); R=$(timeout 1800 z3 "$@" $F 2>&1 | head -1); echo "$* -> $R $(( $(date +%s)-S ))s"; }
run smt.random_seed=1 &
run smt.random_seed=2 &
run smt.random_seed=3 &
run smt.mbqi.max_iterations=100000 &
run smt.relevancy=0 &
run smt.ematching=false &
run smt.macro_finder=true &
run model.compact=false &
wait
