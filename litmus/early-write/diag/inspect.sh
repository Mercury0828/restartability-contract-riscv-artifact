F=/mnt/u22/tmp/isla_candidate_EWBFrfive7five_g0t0_752836_10.smt2
tail -c 1200 $F; echo
echo "forall: $(grep -c forall $F)  exists: $(grep -c exists $F)"
grep -n "set-option\|check-sat\|set-logic" $F | head
diff <(sed 's/[0-9]\+//g' $F) <(sed 's/[0-9]\+//g' /mnt/u22/tmp/isla_candidate_EWBFrfive7five_g0t0_752836_9.smt2) | wc -l
