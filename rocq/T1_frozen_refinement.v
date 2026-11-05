(* T1_frozen_refinement.v — RESTART-V M4: the closed ∀X_F ∃X_N refinement theorem for the frozen
   fragment. The paper-shaped capstone (web-Pro Route-C stopping-rule item 1).

   `frozen_T1_refinement` states: for the frozen fault execution (with the duplicate lane-write pair
   p,q, keeper k = coherence-earlier, deleted d), IF the fault run is consistent (both RVWMO checks)
   and the frozen RO/token modelling hypotheses hold, THEN there EXISTS a no-fault witness execution
   — exhibited as the contracted execution (carrier `contract_carrier d`, reads-from `rf_retarget
   d k rf`) — that

     (i)  passes BOTH RVWMO consistency checks (per-location Cn and main-model Rn acyclic), with NO
          `ppo_lifts` premise (the frozen PPO is discharged inside), AND
     (ii) has the SAME observation: every retained read gets an equal byte value, and every byte's
          coherence-latest write value is preserved.

   Consistency is `T1_frozen.frozen_witness_passes_both_checks`; read-value observation is
   `L1_erasure_preserves_read_values`; final-memory-value observation is
   `Obs_final_state.final_state_preserved_exists`. The witness is CONSTRUCTED (no classical choice).

   HONESTY (unchanged): this is the frozen-fragment T1 as an executable formalization; the fault-run
   consistency and the RO/token modelling hypotheses (po-twin etc.) are antecedents, not derived from
   a concrete instruction model; the handler image is validated separately (cert + Isla, not Rocq);
   and none of this is human-verified (§9.4). Self-contained modulo T1_frozen + L1 + Obs; 0 Admitted /
   0 axioms (Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Obs_final_state.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Rlift_mainmodel.
Require Import RestartV.Frozen_mainmodel.
Require Import RestartV.T1_frozen.
Import ListNotations.

Section T1Refinement.

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte Hart Value : Type.
  Variable gmo : Event -> Event -> Prop.
  Variable is_write is_read is_load is_store : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable wval : Event -> Byte -> Value.
  Variable same_addr addr data ctrl fence : Event -> Event -> Prop.
  Variable hart : Event -> Hart.
  Variable E0 : list Event.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable po poloc : Event -> Event -> Prop.
  Variables p q k d : Event.

  (* gmo well-formedness (irrefl + trans + total) *)
  Hypothesis Hirr : forall e, In e E0 -> ~ gmo e e.
  Hypothesis Htr  : forall a b c, In a E0 -> In b E0 -> In c E0 -> gmo a b -> gmo b c -> gmo a c.
  Hypothesis Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.

  (* duplicate pair / keeper / deleted *)
  Hypothesis d_in : In d E0.
  Hypothesis d_w  : is_write d.
  Hypothesis k_in : In k E0.
  Hypothesis k_w  : is_write k.
  Hypothesis kd_ne : k <> d.
  Hypothesis keeper_before : gmo k d.
  Hypothesis p_in : In p E0.
  Hypothesis q_in : In q E0.
  Hypothesis Hdup : DupPair Event Byte Value is_write touches wval p q.
  Hypothesis Hro  : RO_K Event gmo po p q k.
  Hypothesis Hdpq : d = p \/ d = q.
  Hypothesis Hgamma : forall b, gamma_adj Event Byte is_write touches E0 gmo b p q.
  Hypothesis dup_val : forall b, touches d b -> wval k b = wval d b.

  (* interfaces *)
  Hypothesis rf_is_C4 : forall b r w, is_read r -> In r E0 -> rf w b r ->
      C4_source Event Byte is_write touches gmo po E0 b r w.
  Hypothesis rf_touches : forall w b r, rf w b r -> touches w b.
  Hypothesis rw_disjoint : forall e, is_read e -> is_write e -> False.

  (* frozen RO/token modelling hypotheses *)
  Hypothesis hart_dk : hart d = hart k.
  Hypothesis Hpo_trans : forall a b c, po a b -> po b c -> po a c.  (* po transitivity (CG-2 fix) *)
  Hypothesis Hadj : forall b, touches d b ->
      touches d b /\ touches k b /\
      (forall w, In w E0 -> is_write w -> touches w b -> ~ (gmo k w /\ gmo w d)).
  Hypothesis foot_dk : forall x, touches d x -> touches k x.
  Hypothesis po_twin : forall a b x,
    is_read a -> touches a x -> touches d x -> po a d -> po d b -> po a k /\ po k b.
  Hypothesis rf_functional : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.
  Hypothesis dup_r12 : forall a b bb,
      po a k -> po k b -> (addr a k \/ data a k) -> rf d bb b ->
      po a d /\ po d b /\ (addr a d \/ data a d).

  Let Cn := Clift_coherence.Cn Event Byte gmo is_write is_read touches E0 rf poloc d k.
  Let FRf := Frozen_mainmodel.FRf Event Byte Hart gmo is_write is_read is_load is_store touches
               same_addr addr data ctrl fence hart E0 rf po.
  Let fpw := Frozen_mainmodel.frozen_ppo_wit Event Byte is_write is_read is_load is_store touches
               same_addr addr data ctrl fence E0 rf po d k.
  Let Rn := Rlift_mainmodel.Rn Event Byte Hart gmo is_write is_read touches hart E0 rf fpw d k.
  Let Cf := Clift_coherence.Cf Event Byte gmo is_write is_read touches E0 rf poloc.

  Theorem frozen_T1_refinement :
    (forall x, ~ clos_trans Event Cf x x) ->        (* fault per-location consistent *)
    (forall x, ~ clos_trans Event FRf x x) ->       (* fault main-model consistent *)
    exists (E_N : list Event) (rf_N : Event -> Byte -> Event -> Prop),
      E_N = L1_abstract_erasure.contract_carrier Event eq_ev_dec E0 d /\
      rf_N = L1_abstract_erasure.rf_retarget Event Byte d k rf /\
      (* (i) witness passes BOTH RVWMO acyclicity checks. Cn/Rn are DEFINED over `survivor`
         (= In E_N, by Adapter_L1_witness.survivor_iff_contract) and `rfw` (= rf_N), carrier-restricted
         on EVERY disjunct (round-15 audit refinement), so they ARE EXACTLY the witness's per-location
         / main-model relations — their acyclicity is the witness's RVWMO consistency. *)
      (forall x, ~ clos_trans Event Cn x x) /\
      (forall x, ~ clos_trans Event Rn x x) /\
      (* (i') the witness rf_N satisfies the C4 load-value rule over E_N (L1-consistent execution) *)
      L1_abstract_erasure.L1_consistent Event Byte is_write is_read touches gmo po E_N rf_N /\
      (* (ii-a) observation (memory projection): every retained read keeps its byte value *)
      (forall r b w, In r E_N -> is_read r -> rf w b r ->
         exists w', rf_N w' b r /\ wval w' b = wval w b) /\
      (* (ii-b) observation (memory projection): every byte's coherence-latest WRITTEN value is
         preserved (bytes with no write, and register/CSR/PMP state, are outside this projection). *)
      (forall b w_f,
         co_max_of Event Byte gmo is_write touches (inE0 Event E0) b w_f ->
         exists w_n, co_max_of Event Byte gmo is_write touches (survivor Event E0 d) b w_n /\
                     wval w_f b = wval w_n b).
  Proof.
    intros Hcf Hfrf.
    exists (L1_abstract_erasure.contract_carrier Event eq_ev_dec E0 d).
    exists (L1_abstract_erasure.rf_retarget Event Byte d k rf).
    split; [reflexivity|]. split; [reflexivity|].
    (* consistency, both checks, ppo discharged *)
    destruct (T1_frozen.frozen_witness_passes_both_checks Event eq_ev_dec Byte Hart gmo
                is_write is_read is_load is_store touches same_addr addr data ctrl fence hart E0 rf
                po poloc d k d_in d_w k_in k_w kd_ne rf_touches keeper_before hart_dk Htot Hadj
                foot_dk po_twin rf_functional dup_r12 Hcf Hfrf) as [Hcn Hrn].
    split; [exact Hcn|]. split; [exact Hrn|].
    split.
    { (* witness L1-consistency: rf_N satisfies the C4 load-value rule over E_N *)
      exact (L1_abstract_erasure.L1_erasure_preserves_consistency Event eq_ev_dec Byte Value
               is_write is_read touches wval E0 gmo rf po rf_is_C4 rw_disjoint
               (L1_abstract_erasure.Build_gmo_wf Event E0 gmo Hirr Htr Htot) Hpo_trans
               p q k d p_in q_in Hdup Hro Hgamma Hdpq kd_ne). }
    split.
    - (* read-value observation *)
      intros r b w Hr Hrd Hrf.
      exact (L1_abstract_erasure.L1_erasure_preserves_read_values Event eq_ev_dec Byte Value
               is_write is_read touches wval E0 gmo rf po rf_is_C4 rf_touches
               (L1_abstract_erasure.Build_gmo_wf Event E0 gmo Hirr Htr Htot)
               p q k d r b w Hdup Hro Hdpq kd_ne Hr Hrd Hrf).
    - (* final-memory-value observation *)
      intros b w_f Hmax.
      exact (Obs_final_state.final_state_preserved_exists Event eq_ev_dec Byte Value gmo is_write
               touches wval E0 d k k_in k_w kd_ne foot_dk dup_val
               (fun b0 Hdb0 => proj2 (proj2 (Hadj b0 Hdb0)))
               (Obs_final_state.Build_gmo_wf Event gmo E0 Hirr Htr Htot)
               b w_f Hmax).
  Qed.

End T1Refinement.
