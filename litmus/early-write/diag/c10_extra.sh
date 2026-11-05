# check that the option works when placed where isla puts --extra-smt (after the assertions, before check-sat)
F=/tmp/isla_candidate_EWBFrfive7five_g0t0_752836_10.smt2
G=/tmp/c10_extra.smt2
awk 'BEGIN{d=0} /^\(check-sat\)/ && !d {print "(set-option :smt.macro_finder true)"; d=1} {print}' $F > $G
S=$(date +%s); timeout 600 z3 -T:2400 $G 2>&1 | head -2 | cut -c1-200; echo "$(( $(date +%s)-S ))s"
