#!/usr/bin/env bash
# verify.sh — RESTART-V M4 one-command Rocq reproducibility harness.
# Builds every file in dependency order under -Q . RestartV, then runs `Print Assumptions` on the
# headline theorems and checks each reports "Closed under the global context" (0 Admitted / 0 axioms).
# Run from the rocq/ directory in the Coq environment (e.g. WSL Ubuntu with Coq 8.15).
#   bash verify.sh
# Exit 0 iff all files compile AND every headline theorem is axiom-free.

set -u
FILES=(
  L1_abstract_erasure L1b_edge_lift
  L2_gamma L2_consistency L2_ppo
  L3_handler L4_restart
  Clift_coherence Rlift_mainmodel Obs_final_state
  Adapter_L1_witness PPO_frozen PPO_union R2_counterexample Token_model Reexec_orientation Duplicate_facts Frozen_mainmodel
  Top_T1_skeleton T1_consistency T1_frozen T1_frozen_refinement T1_frozen_instantiated
  CG2_concrete_instance WIT1_nofault_lift Ctx_erasure Stage2_normal_candidate Stage2_state_chain
  Stage2_obligations Frozen_pmp Stage2_composed Stage2_endtoend Stage2_endtoend_v2
  Multi_lane Multi_lane_instance Alpha_regs Alpha_regs_instance
  ML_base ML_T1 ML_instance ML_stage2 ML_instance_stage2 Gamma_adj_needed
  Perbyte Perbyte_example Gamma_adj_obs Pmp_partial Normal_instance ML_instance_pb ML_instance_2h ML_instance_unord
)
# headline theorem : file that defines it
declare -A HEADLINE=(
  [frozen_T1_refinement]=T1_frozen_refinement
  [frozen_T1_refinement_instantiated]=T1_frozen_instantiated
  [frozen_witness_passes_both_checks]=T1_frozen
  [frozen_witness_mainmodel_acyclic]=Frozen_mainmodel
  [ppo_wit_lifts]=PPO_union
  [r2N_sub_r2F]=PPO_frozen
  [witness_perloc_acyclic]=Clift_coherence
  [L1_erasure_preserves_read_values]=L1_abstract_erasure
  [final_state_preserved_exists]=Obs_final_state
  [alleged_counterexample_is_cyclic]=R2_counterexample
  [po_twin_derived]=Token_model
  [dup_r12_derived]=Token_model
  [foot_dk_from_DupPair]=Duplicate_facts
  [replay_keeper_impossible_under_reexec]=Reexec_orientation
  [first_before_replay_gmo]=Reexec_orientation
  [cg2_concrete_instance]=CG2_concrete_instance
  [cg2_stage2_observation]=CG2_concrete_instance
  [wit1_nofault_lift]=WIT1_nofault_lift
  [general_ctx_erasure]=Ctx_erasure
  [stage2_normal_candidate]=Stage2_normal_candidate
  [stage2_statewf_reduction]=Stage2_state_chain
  [O2_closed]=Stage2_obligations
  [O3_reads_keep_values]=Stage2_obligations
  [frozen_pmp_lane_checks_succeed]=Frozen_pmp
  [stage2_composed]=Stage2_composed
  [stage2_endtoend]=Stage2_endtoend
  [stage2_endtoend_v2]=Stage2_endtoend_v2
  [retarget_preserves_C4]=Multi_lane
  [erase_all_preserves_C4]=Multi_lane
  [erase_all_preserves_values]=Multi_lane
  [i_lanes_ok]=Multi_lane_instance
  [i_C4_survives]=Multi_lane_instance
  [i_value_byte0]=Multi_lane_instance
  [i_sources_are_keepers]=Multi_lane_instance
  [alpha_regs_gives_Dup]=Alpha_regs
  [alpha_regs_gives_lane_conditions]=Alpha_regs
  [ar_i_alpha]=Alpha_regs_instance
  [ar_i_alpha_fails_when_data_clobbered]=Alpha_regs_instance
  [ar_i_dup]=Alpha_regs_instance
  [ar_i_lane_conditions]=Alpha_regs_instance
  [ML_T1_refinement]=ML_T1
  [ML_T1_refinement_instantiated]=ML_T1
  [ML_T1_covers_single_lane]=ML_T1
  [single_carrier]=ML_T1
  [single_rf]=ML_T1
  [ml_concrete_instance]=ML_instance
  [ml_instance_observation]=ML_instance
  [natural_order_breaks_global_adj]=ML_instance
  [ML_stage2_endtoend]=ML_stage2
  [ml_stage2_instance]=ML_instance_stage2
  [gamma_adj_needed_full]=Gamma_adj_needed
  [gamma_D_implies_gamma_adj]=L2_gamma
  [Main_model_acyclic]=L2_consistency
  [union_to_perbyte]=Perbyte
  [rvwmo_perbyte_coherence]=Perbyte
  [ML_T1_refinement_pb]=Perbyte
  [ML_stage2_endtoend_pb]=Perbyte
  [ex_perbyte_ok]=Perbyte_example
  [ex_union_cycle]=Perbyte_example
  [ex_load_value]=Perbyte_example
  [gamma_adj_needed_obs]=Gamma_adj_obs
  [allows_iff_deciding_full]=Pmp_partial
  [spec_example_denied]=Pmp_partial
  [spec_example_bytes_writable]=Pmp_partial
  [frozen_lanes_never_partial]=Pmp_partial
  [normal_instance]=Normal_instance
  [ml_T1_pb_instance]=ML_instance_pb
  [ml_stage2_pb_instance]=ML_instance_pb
  [ml_normal_instance]=ML_instance_pb
  [ml2_T1_pb_instance]=ML_instance_2h
  [ml2_instance_observation]=ML_instance_2h
  [ml2_stage2_instance]=ML_instance_2h
  [ml2_stage2_pb_instance]=ML_instance_2h
  [ml2_normal_instance]=ML_instance_2h
  [normal_instance_pos]=Normal_instance
  [mu_T1_pb_instance]=ML_instance_unord
  [mu_stage2_pb_instance]=ML_instance_unord
  [mu_stage2_instance]=ML_instance_unord
  [mu_normal_instance]=ML_instance_unord
  [mu_instance_observation]=ML_instance_unord
  [mu_po_not_total]=ML_instance_unord
)

rm -f ./*.vo ./*.vok ./*.vos ./*.glob ./.*.aux 2>/dev/null
fail=0

echo "== compiling =="
for f in "${FILES[@]}"; do
  if coqc -Q . RestartV "$f.v" >/dev/null 2>&1; then
    echo "  ok   $f"
  else
    echo "  FAIL $f"; coqc -Q . RestartV "$f.v" 2>&1 | head -5; fail=1
  fi
done
[ "$fail" = 1 ] && { echo "BUILD FAILED"; exit 1; }

echo "== Print Assumptions (headline theorems must be axiom-free) =="
for thm in "${!HEADLINE[@]}"; do
  f="${HEADLINE[$thm]}"
  tmp="$(mktemp /tmp/pa_XXXX.v)"
  { cat "$f.v"; printf '\nPrint Assumptions %s.\n' "$thm"; } > "$tmp"
  out="$(coqc -Q . RestartV "$tmp" 2>&1 | tail -3)"
  rm -f "$tmp"
  if echo "$out" | grep -q "Closed under the global context"; then
    echo "  0-axiom  $thm"
  else
    echo "  AXIOMS?  $thm -> $out"; fail=1
  fi
done

[ "$fail" = 0 ] && echo "ALL GREEN: ${#FILES[@]} files build, ${#HEADLINE[@]} headline theorems 0-axiom." || echo "VERIFY FAILED"
exit $fail
