(* Stage2_composed.v — RESTART-V: the MECHANIZED composition of the Stage-2 layers.

   ===================================================================================================
   WHY THIS FILE EXISTS — THE LAYERS WERE PREVIOUSLY *UNWIRED*
   ===================================================================================================
   Before this file, each Stage-2 layer was an INDEPENDENT abstract Section with its OWN carrier
   parameter, and NO theorem anywhere instantiated one layer's OUTPUT as the next layer's INPUT:

     * `L1_abstract_erasure` produced `contract_carrier E0 d` / `rf_retarget d k rf` — and nothing
       related them to anything downstream;
     * `Ctx_erasure` took a bare `Variable E : list Event` ("the contracted carrier X_C coming out of
       Stage 1", per its comment) — but that was a COMMENT, not a substitution;
     * `Stage2_normal_candidate` took a bare `Variable EK : list Event` ("the trap-free memory kernel
       handed over by Ctx_erasure") — again a comment, not a substitution;
     * `Stage2_state_chain` took a bare `Variable NEvT : Type`.

   So the "Stage-2 chain" was a CONCEPTUAL composition: four theorems that a reader was invited to
   believe fit together.  THIS FILE MAKES IT A MECHANIZED ONE.  It defines the carrier chain
   explicitly and re-derives every conjunct by APPLYING the corresponding layer theorem AT THE WIRED
   CARRIERS — nothing below is restated, re-proved by hand, or asserted:

       E0  --(Stage 1: drop the replay duplicate d)-->  E_C
           --(Ctx_erasure: drop the trap region Ctx)-->  E_K
           --(Layer 3: drop the checks, relabel, generate NChk)-->  E_N

   ===================================================================================================
   WHAT THE COMPOSITION ADDS — AND WHAT IT DOES **NOT** ADD
   ===================================================================================================
   IT ADDS exactly two things:
     (i)  THE CARRIER WIRING.  `E_C`, `rf_C`, `E_K`, `E_N` are DEFINITIONS, each literally the previous
          layer's output term, and the carrier nesting `E_N <- E_K <- E_C <- E0` is PROVED (by applying
          the layers' own membership lemmas), not assumed.
     (ii) THE END-TO-END TRANSFER.  Per-location acyclicity travels from the FAULT run's carrier `E_C`
          all the way to the normal candidate `E_N`, and the byte-wise memory projection (`co_max_of`)
          is shown EQUAL at `E_C` and at `E_N`, by chaining the layers' own transfer theorems.

   IT ADDS **NO NEW SEMANTIC CONTENT**.  Every conjunct below is an application of a theorem that was
   already proved in its own layer; this file introduces no new hypothesis of its own beyond the UNION
   of the layers' named antecedents (listed in §0.3 below), and proves no new fact about RISC-V,
   RVWMO, PMP or the handler.

   IN PARTICULAR, THE COMPOSITION DOES **NOT** UPGRADE THE RESULT TO
   "THERE EXISTS A NO-FAULT **EXECUTION**".  Specifically, and unchanged by wiring:
     - `Cand_N_struct` is Layer 3's STRUCTURAL rendering of the no-fault candidate class and is
       STRICTLY WEAKER than the operational D-a `Cand_N` (which is stated over the operational model
       together with `StateWF`).  It must never be cited as `Cand_N`.
     - The generated per-lane checks `NChk l` are asserted successful BY DEFINITION
       (`chk_ok_N (NChk _) := True`).  That is a label, not a verdict computed against the repaired
       PMP state.
     - Layer 4 supplies only the STRUCTURAL half of `StateWF` (chain existence + determinism, hole-free
       and generated).  The semantic residue O1 (`step` is the real transition function), O2 (the
       generated checks really succeed) and O3 (normal load values agree) is NAMED and OPEN, as are
       decoding, token conformance, the precise-state condition and the full final-state construction.
     - O1-c and B5 are UNCHANGED by this file.
     - `E_N` is a member of `Cand_N_struct`, NOT of the operational `Cand_N`; nothing here constructs an
       execution, a state chain over the REAL semantics, or a trap-free operational run.

   NOTE ON THE VALUE HALF.  Layer 3's `transport_rf` is a DEFINITIONAL IDENTITY (`rf_N (NKeep w) b
   (NKeep r)` is by definition `rf w b r`), so it carries no value content of its own.  The value half
   of the story is STAGE 1's: `L1_erasure_preserves_read_values`, applied here at the wired chain
   (conjunct 3 of the headline), is what says every retained read still has a source of EQUAL byte
   value under `rf_C`.

   ===================================================================================================
   §0.3  THE NAMED ANTECEDENTS THE COMPOSED THEOREM CARRIES (the UNION of the layers')
   ===================================================================================================
   From Stage 1 (`L1_abstract_erasure`):
       H_rf_is_C4, H_rf_touches, H_rw_disjoint, H_gmo_wf, H_po_trans,
       H_p_in, H_q_in, H_dup (DupPair p q), H_rok (RO_K p q k), H_gamma (gamma_adj at every byte),
       H_d_is_dup (d = p \/ d = q), H_k_ne_d.
   From `Ctx_erasure`:
       H_ctx_silent   (the `Hschema` consequence — a NAMED ANTECEDENT, `Hschema` itself is unmechanized).
   From `Stage2_normal_candidate` (Layer 3):
       H_kernel_one_write_per_lane  (instantiated AT `E_K`, i.e. at the wired kernel),
       H_chk_nonmem, H_lane_write_is_write.
   From `Stage2_state_chain` (Layer 4):
       NONE — its structural half has an EMPTY antecedent list, so wiring it costs nothing.

   ===================================================================================================
   §0.4  THE ONE SEAM THAT IS NOT FLUSH — AND HOW IT IS CLOSED *BY A LAYER THEOREM*
   ===================================================================================================
   `Ctx_erasure` hands out results at the carrier `EK`.  Layer 3, however, does NOT consume `EK`
   directly: its per-location relation `CfK` and its `co_max` transport are stated at
   `mem_kernel = EK` MINUS the check events.  So the two interfaces are NOT literally flush; a bridge
   from `EK` to `mem_kernel` is required, and neither layer exposes one.

   That bridge is NOT hand-rolled here.  It is obtained by APPLYING `Ctx_erasure.general_ctx_erasure`
   A SECOND TIME, at `E := E_K`, `Ctx := is_chk`, `ctx_dec := chk_dec`, because:
     * `Ctx_erasure.EK Event E_K is_chk chk_dec` is DEFINITIONALLY EQUAL to
       `Stage2_normal_candidate.mem_kernel Event E_K is_chk chk_dec` (both are the same `filter`), and
       likewise `Ctx_erasure.CfEK ... E_K is_chk chk_dec` is definitionally `Stage2_normal_candidate.CfK`;
     * the second instance's `ctx_silent` antecedent at `is_chk` is LITERALLY Layer 3's `chk_nonmem`.
   So the check-erasure step is the SAME theorem as the trap-erasure step, applied at a second region.
   No new lemma, no new hypothesis.

   0 Admitted / 0 axioms (`Print Assumptions stage2_composed`).  Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Obs_final_state.
Require Import RestartV.Ctx_erasure.
Require Import RestartV.Stage2_normal_candidate.
Require Import RestartV.Stage2_state_chain.
Import ListNotations.

Section Stage2Composed.

  (* ===================================================================== *)
  (* 0.  The shared abstract interface                                      *)
  (* ===================================================================== *)

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte Value Lane : Type.
  Variable gmo po poloc : Event -> Event -> Prop.
  Variable is_read is_write : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable wval : Event -> Byte -> Value.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable E0 : list Event.                    (* the FAULT run's carrier *)
  Variables p q k d : Event.                   (* duplicate pair, keeper, deleted *)
  Variable Ctx : Event -> Prop.                (* the trap region *)
  Variable ctx_dec : forall e, {Ctx e} + {~ Ctx e}.
  Variable is_chk : Event -> Prop.             (* PMP check events of the fault run *)
  Variable chk_dec : forall e, {is_chk e} + {~ is_chk e}.
  Variable lane : Event -> Lane.
  Variable is_lane_write : Event -> Prop.
  Variable lanes : list Lane.

  (* ===================================================================== *)
  (* 1.  THE CARRIER CHAIN — each definition IS the previous layer's output *)
  (* ===================================================================== *)

  (* Stage 1: erase the replay duplicate `d`, retarget rf to the keeper `k`. *)
  Definition E_C : list Event :=
    L1_abstract_erasure.contract_carrier Event eq_ev_dec E0 d.
  Definition rf_C : Event -> Byte -> Event -> Prop :=
    L1_abstract_erasure.rf_retarget Event Byte d k rf.

  (* Ctx_erasure, applied AT Stage 1's output: erase the trap region. *)
  Definition E_K : list Event :=
    Ctx_erasure.EK Event E_C Ctx ctx_dec.

  (* Layer 3, applied AT the Ctx-erased carrier: the normal candidate. *)
  Definition E_N : list (Stage2_normal_candidate.NEv Event Lane) :=
    Stage2_normal_candidate.EN' Event Lane E_K is_chk chk_dec lanes.

  (* The intermediate carrier Layer 3 actually consumes (E_K minus the checks). *)
  Definition E_MK : list Event :=
    Stage2_normal_candidate.mem_kernel Event E_K is_chk chk_dec.

  (* The per-location relations at each link of the chain, named with the LAYERS' OWN definitions. *)
  Definition Cf_C  := Ctx_erasure.CfE Event Byte gmo poloc is_read is_write touches rf_C E_C.
  Definition Cf_K  := Ctx_erasure.CfE Event Byte gmo poloc is_read is_write touches rf_C E_K.
  Definition Cf_MK := Stage2_normal_candidate.CfK Event Byte gmo poloc is_read is_write touches
                        rf_C E_K is_chk chk_dec.
  Definition Cf_N  := Stage2_normal_candidate.CfN Event Byte Lane gmo poloc is_read is_write touches
                        rf_C E_K is_chk chk_dec lanes.

  (* ===================================================================== *)
  (* 2.  THE NAMED ANTECEDENTS (union of the layers'; see header §0.3)      *)
  (* ===================================================================== *)

  (* ---- Stage 1 ---- *)
  Hypothesis H_rf_is_C4 :
    forall b r w, is_read r -> In r E0 -> rf w b r ->
      L1_abstract_erasure.C4_source Event Byte is_write touches gmo po E0 b r w.
  Hypothesis H_rf_touches : forall w b r, rf w b r -> touches w b.
  Hypothesis H_rw_disjoint : forall e, is_read e -> is_write e -> False.
  Hypothesis H_gmo_wf : L1_abstract_erasure.gmo_wf Event E0 gmo.
  Hypothesis H_po_trans : forall a b c, po a b -> po b c -> po a c.
  Hypothesis H_p_in : In p E0.
  Hypothesis H_q_in : In q E0.
  Hypothesis H_dup : L1_abstract_erasure.DupPair Event Byte Value is_write touches wval p q.
  Hypothesis H_rok : L1_abstract_erasure.RO_K Event gmo po p q k.
  Hypothesis H_gamma :
    forall b, L1_abstract_erasure.gamma_adj Event Byte is_write touches E0 gmo b p q.
  Hypothesis H_d_is_dup : d = p \/ d = q.
  Hypothesis H_k_ne_d : k <> d.

  (* ---- Ctx_erasure (the `Hschema` consequence; `Hschema` itself is unmechanized) ---- *)
  Hypothesis H_ctx_silent :
    forall e, Ctx e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b).

  (* ---- Layer 3.  NOTE: instantiated AT THE WIRED KERNEL `E_K`, not at a free carrier. ---- *)
  Hypothesis H_kernel_one_write_per_lane :
    forall l, In l lanes ->
      exists w, In w E_K /\ is_lane_write w /\ lane w = l /\
                (forall w', In w' E_K -> is_lane_write w' -> lane w' = l -> w' = w).
  Hypothesis H_chk_nonmem :
    forall e, is_chk e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b).
  Hypothesis H_lane_write_is_write : forall e, is_lane_write e -> is_write e.

  (* ===================================================================== *)
  (* 3.  THE LAYER INSTANCES — every one an APPLICATION at the wired chain  *)
  (* ===================================================================== *)

  (* Stage 1 at (E0, rf) -> (E_C, rf_C). *)
  Definition LAYER1 :
    L1_abstract_erasure.L1_consistent Event Byte is_write is_read touches gmo po E_C rf_C :=
    L1_abstract_erasure.L1_erasure_preserves_consistency
      Event eq_ev_dec Byte Value is_write is_read touches wval E0 gmo rf po
      H_rf_is_C4 H_rw_disjoint H_gmo_wf H_po_trans
      p q k d H_p_in H_q_in H_dup H_rok H_gamma H_d_is_dup H_k_ne_d.

  (* Ctx_erasure at (E := E_C, rf := rf_C, Ctx := Ctx):  E_C -> E_K. *)
  Definition LAYER2_trap :=
    Ctx_erasure.general_ctx_erasure
      Event Byte gmo po poloc is_read is_write touches rf_C E_C Ctx ctx_dec H_ctx_silent.

  (* Ctx_erasure AGAIN at (E := E_K, rf := rf_C, Ctx := is_chk):  E_K -> E_MK.
     See header §0.4: this is the seam bridge, and it is a LAYER THEOREM APPLICATION, not a new proof.
     Its `ctx_silent` antecedent at `is_chk` is literally Layer 3's `chk_nonmem`. *)
  Definition LAYER2_chk :=
    Ctx_erasure.general_ctx_erasure
      Event Byte gmo po poloc is_read is_write touches rf_C E_K is_chk chk_dec H_chk_nonmem.

  (* Layer 3 at (EK := E_K, rf := rf_C):  E_K -> E_N. *)
  Definition LAYER3 :=
    Stage2_normal_candidate.stage2_normal_candidate
      Event Byte Lane gmo poloc is_read is_write touches rf_C E_K
      lane is_lane_write is_chk chk_dec lanes
      H_kernel_one_write_per_lane H_chk_nonmem H_lane_write_is_write.

  (* Layer 4 at (NEvT := Layer 3's normal event universe). *)
  Definition LAYER4 :=
    Stage2_state_chain.stage2_statewf_reduction (Stage2_normal_candidate.NEv Event Lane).

  (* ===================================================================== *)
  (* 4.  THE CARRIERS REALLY DO NEST — proved by applying the layers'       *)
  (*     OWN membership lemmas at the wired carriers                        *)
  (* ===================================================================== *)

  Lemma E_C_sub_E0 : forall e, In e E_C -> In e E0.
  Proof. exact (L1_abstract_erasure.contract_carrier_sub Event eq_ev_dec E0 d). Qed.

  Lemma E_K_sub_E_C : forall e, In e E_K -> In e E_C.
  Proof. exact (Ctx_erasure.EK_sub Event E_C Ctx ctx_dec). Qed.

  Lemma E_MK_sub_E_K : forall e, In e E_MK -> In e E_K.
  Proof. exact (Ctx_erasure.EK_sub Event E_K is_chk chk_dec). Qed.

  Lemma E_K_trap_free : forall e, In e E_K -> ~ Ctx e.
  Proof. exact (proj1 LAYER2_trap). Qed.

  (* the last link: the injection into the normal event universe *)
  Lemma E_N_has_NKeep :
    forall e, In e E_K -> ~ is_chk e -> In (Stage2_normal_candidate.NKeep Event Lane e) E_N.
  Proof.
    intros e He Hc.
    exact (proj2 (Stage2_normal_candidate.In_NKeep_iff
                    Event Lane E_K is_chk chk_dec lanes e) (conj He Hc)).
  Qed.

  (* ===================================================================== *)
  (* 5.  END-TO-END ACYCLICITY: fault carrier -> normal candidate           *)
  (*     three layer applications in a row, no hand proof                   *)
  (* ===================================================================== *)

  Lemma composed_acyclicity :
    (forall x, ~ clos_trans Event Cf_C x x) ->
    (forall n, ~ clos_trans (Stage2_normal_candidate.NEv Event Lane) Cf_N n n).
  Proof.
    intro Hacyc_C.
    (* Ctx_erasure @ E_C: acyclicity at E_C transfers to acyclicity at E_K *)
    assert (Hacyc_K : forall x, ~ clos_trans Event Cf_K x x)
      by exact (proj1 (proj2 (proj2 LAYER2_trap)) Hacyc_C).
    (* Ctx_erasure @ E_K with Ctx := is_chk: acyclicity at E_K transfers to acyclicity at E_MK *)
    assert (Hacyc_MK : forall x, ~ clos_trans Event Cf_MK x x)
      by exact (proj1 (proj2 (proj2 LAYER2_chk)) Hacyc_K).
    (* Layer 3: acyclicity at E_MK transfers to acyclicity at E_N *)
    exact (proj1 (proj2 LAYER3) Hacyc_MK).
  Qed.

  (* ===================================================================== *)
  (* 6.  END-TO-END MEMORY PROJECTION: co_max at E_C = co_max at E_N        *)
  (*     three layer applications in a row, no hand proof                   *)
  (* ===================================================================== *)

  Lemma composed_co_max : forall b w,
    Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E_C) b w
    <-> Obs_final_state.co_max_of (Stage2_normal_candidate.NEv Event Lane) Byte
          (Stage2_normal_candidate.gmo_N Event Lane gmo)
          (Stage2_normal_candidate.is_write_N Event Lane is_write)
          (Stage2_normal_candidate.touches_N Event Byte Lane touches)
          (fun n => In n E_N) b (Stage2_normal_candidate.NKeep Event Lane w).
  Proof.
    intros b w.
    (* Ctx_erasure @ E_C : co_max at E_C  <->  co_max at E_K *)
    pose proof (proj2 (proj2 (proj2 (proj2 LAYER2_trap))) b w) as Hcm1.
    (* Ctx_erasure @ E_K (Ctx := is_chk) : co_max at E_K  <->  co_max at E_MK *)
    pose proof (proj2 (proj2 (proj2 (proj2 LAYER2_chk))) b w) as Hcm2.
    (* Layer 3 : co_max at E_MK  <->  co_max at E_N (along NKeep) *)
    pose proof (proj2 (proj2 (proj2 (proj2 LAYER3))) b w) as Hcm3.
    split.
    - intro H. apply Hcm3. apply Hcm2. apply Hcm1. exact H.
    - intro H. apply Hcm1. apply Hcm2. apply Hcm3. exact H.
  Qed.

  (* ===================================================================== *)
  (* 7.  END-TO-END READ VALUES (the value half is STAGE 1's)               *)
  (* ===================================================================== *)

  Lemma composed_read_values :
    forall r b w, In r E_C -> is_read r -> rf w b r ->
      exists w', rf_C w' b r /\ wval w' b = wval w b.
  Proof.
    intros r b w Hr Hrd Hrf.
    exact (L1_abstract_erasure.L1_erasure_preserves_read_values
             Event eq_ev_dec Byte Value is_write is_read touches wval E0 gmo rf po
             H_rf_is_C4 H_rf_touches H_gmo_wf
             p q k d r b w H_dup H_rok H_d_is_dup H_k_ne_d Hr Hrd Hrf).
  Qed.

  (* ===================================================================== *)
  (* 8.  HEADLINE — every conjunct is a LAYER THEOREM APPLIED AT THE CHAIN  *)
  (* ===================================================================== *)

  Theorem stage2_composed :
    (* --- 1. the carrier chain really nests: E_N <- E_K <- E_C <- E0 --- *)
    ((forall e, In e E_C -> In e E0)
     /\ (forall e, In e E_K -> In e E_C)
     /\ (forall e, In e E_K -> ~ is_chk e ->
           In (Stage2_normal_candidate.NKeep Event Lane e) E_N))
    (* --- 2. Stage 1: the contracted graph is L1-consistent at (E_C, rf_C) --- *)
    /\ L1_abstract_erasure.L1_consistent Event Byte is_write is_read touches gmo po E_C rf_C
    (* --- 3. Stage 1 (value half): every retained read keeps an equal-valued source --- *)
    /\ (forall r b w, In r E_C -> is_read r -> rf w b r ->
          exists w', rf_C w' b r /\ wval w' b = wval w b)
    (* --- 4. Ctx_erasure @ E_C: the kernel is trap-free --- *)
    /\ (forall e, In e E_K -> ~ Ctx e)
    (* --- 5. Ctx_erasure @ E_C: the per-location relations at E_C and E_K COINCIDE --- *)
    /\ (forall x y,
          Ctx_erasure.CfEK Event Byte gmo poloc is_read is_write touches rf_C E_C Ctx ctx_dec x y
          <-> Cf_C x y)
    (* --- 6. Ctx_erasure @ E_C: intervening stores reflect (the r2 hazard is absent) --- *)
    /\ (forall b a c,
          Ctx_erasure.store_between_on Event Byte po is_write touches (fun e => In e E_C) b a c
          <-> Ctx_erasure.store_between_on Event Byte po is_write touches (fun e => In e E_K) b a c)
    (* --- 7. Layer 3 @ E_K: the normal candidate is STRUCTURALLY normal
             (NOT the operational Cand_N — see header) --- *)
    /\ Stage2_normal_candidate.Cand_N_struct Event Lane E_K lane is_lane_write is_chk chk_dec lanes
    (* --- 8. Layer 3 @ E_K: the gmo / rf transports along NKeep
             (`transport_rf` is a definitional identity — see header) --- *)
    /\ (forall a b, Stage2_normal_candidate.gmo_N Event Lane gmo
                      (Stage2_normal_candidate.NKeep Event Lane a)
                      (Stage2_normal_candidate.NKeep Event Lane b) <-> gmo a b)
    /\ (forall w b r, Stage2_normal_candidate.rf_N Event Byte Lane rf_C
                        (Stage2_normal_candidate.NKeep Event Lane w) b
                        (Stage2_normal_candidate.NKeep Event Lane r) <-> rf_C w b r)
    (* --- 9. END TO END: fault-carrier per-location acyclicity => normal-candidate acyclicity --- *)
    /\ ((forall x, ~ clos_trans Event Cf_C x x) ->
        (forall n, ~ clos_trans (Stage2_normal_candidate.NEv Event Lane) Cf_N n n))
    (* --- 10. END TO END: the byte-wise memory projection is preserved along the WHOLE chain --- *)
    /\ (forall b w,
          Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E_C) b w
          <-> Obs_final_state.co_max_of (Stage2_normal_candidate.NEv Event Lane) Byte
                (Stage2_normal_candidate.gmo_N Event Lane gmo)
                (Stage2_normal_candidate.is_write_N Event Lane is_write)
                (Stage2_normal_candidate.touches_N Event Byte Lane touches)
                (fun n => In n E_N) b (Stage2_normal_candidate.NKeep Event Lane w))
    (* --- 11. Layer 4 @ Layer 3's event universe: the STRUCTURAL half of StateWF, for every
              normal event list, with an EMPTY antecedent list (see header: this is NOT StateWF) --- *)
    /\ (forall (St : Type) (step : St -> Stage2_normal_candidate.NEv Event Lane -> St)
               (init : St) (l : list (Stage2_normal_candidate.NEv Event Lane)),
          Stage2_state_chain.StateWF_struct (Stage2_normal_candidate.NEv Event Lane) St step init l).
  Proof.
    split.
    { split; [ exact E_C_sub_E0 | ].
      split; [ exact E_K_sub_E_C | exact E_N_has_NKeep ]. }
    split; [ exact LAYER1 | ].
    split; [ exact composed_read_values | ].
    split; [ exact E_K_trap_free | ].
    split; [ exact (proj1 (proj2 LAYER2_trap)) | ].
    split; [ exact (proj1 (proj2 (proj2 (proj2 LAYER2_trap)))) | ].
    split; [ exact (proj1 LAYER3) | ].
    split; [ exact (proj1 (proj2 (proj2 LAYER3))) | ].
    split; [ exact (proj1 (proj2 (proj2 (proj2 LAYER3)))) | ].
    split; [ exact composed_acyclicity | ].
    split; [ exact composed_co_max | ].
    intros St step init l.
    exact (proj1 (LAYER4 St step init l)).
  Qed.

End Stage2Composed.

(* All lemmas Qed-proved; 0 Admitted.  The Stage-2 layers are now WIRED: E0 -> E_C -> E_K -> E_N,
   with every conjunct of `stage2_composed` obtained by APPLYING a layer theorem at the wired
   carriers.  Read the header before quoting anything: this adds carrier wiring and end-to-end
   transfer ONLY, and does NOT establish "there exists a no-fault EXECUTION". *)
