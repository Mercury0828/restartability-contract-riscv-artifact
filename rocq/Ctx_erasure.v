(* Ctx_erasure.v — RESTART-V: the GENERAL (∀, fully abstract) *memory half* of the Stage-2 lift.

   WHAT THIS FILE IS.  `WIT1_nofault_lift` exhibits a trap-free witness for ONE concrete
   execution (the CG-2 7-event instance).  This file is the ∀ version of the memory half:
   for ANY contracted carrier `E` and ANY trap region `Ctx` over ANY abstract event/byte model,
   deleting `Ctx` from the carrier
     (a) leaves the RVWMO per-location relation LITERALLY UNCHANGED (an iff, not an inclusion),
         hence per-location acyclicity transfers;
     (b) reflects intervening stores (`store_between`) in both directions, so the r2 / `polnw`
         anti-monotonicity obstruction never arises;
     (c) preserves the memory projection (`co_max_of` per byte, and rf sourcing).
   It is a Section over Variables (like `Clift_coherence.v`) — that generality is the entire point;
   it is deliberately NOT built on the concrete CG-2 model.

   The proof is by COMPOSITION + ISOMORPHISM, not by re-deriving the r2 lift.  The reason it works:
   `Ctx` is RVWMO-silent, so no RVWMO *write* is erased; therefore `store_between` keeps every
   witness, therefore `polnw`/r2 are unchanged, therefore the anti-monotonicity obstruction that
   bites when you delete a *write* simply does not arise here; and the per-location relations
   coincide, so acyclicity transfers by equality (a fortiori as a subrelation).

   ON `ctx_silent` (the load-bearing antecedent).  `ctx_silent` says every `Ctx` event is neither a
   read nor a write and touches no byte.  This is a CONSEQUENCE of the ALREADY-FROZEN handler schema
   `Hschema` — the successful trap path contains no regular-memory / vector / fence / AMO / LR-SC /
   annotated event, only CSR accesses — and is NOT a fresh contract commitment.  However `Hschema`
   itself lives in the UNMECHANIZED OPERATIONAL LAYER of this development.  So here `ctx_silent` is
   a NAMED ANTECEDENT (a Section Hypothesis, i.e. a ∀-bound premise of every theorem below), not a
   discharged fact.  The assumption report must be read with that in mind: "0 axioms" means nothing
   is smuggled in past the interface, NOT that `Hschema` has been proved.

   EXTRA INTERFACE HYPOTHESIS BEYOND THE COMMISSIONED LIST — FLAGGED.  Besides the commissioned
   `ctx_silent`, `poloc_touches`, `rf_src_write`, this file needs ONE more, exactly as the brief
   anticipated:
       rf_tgt_read : forall w b r, rf w b r -> is_read r
   It is required only by `ctx_not_in_Cf`, for the `rf` disjunct: the abstract `rf` interface gives
   `touches`/`is_write` for the SOURCE but says nothing about the TARGET, so there is no other way to
   contradict `Ctx` on the target of an rf edge.  It is a basic typing fact of any RVWMO event
   structure (an rf edge lands on a read).  It is NOT used by the headline `general_ctx_erasure`
   conjunction: as the printed type shows, `general_ctx_erasure` takes exactly ONE antecedent,
   `ctx_silent`, and neither `poloc_touches` nor `rf_src_write` nor `rf_tgt_read`.  `rf_tgt_read` and
   `poloc_touches` are premises of `ctx_not_in_Cf` only; `rf_src_write` of `ctx_not_in_Cf` and
   `erase_ctx_preserves_rf` only.  So the extra hypothesis does not weaken the headline result.

   WHAT THIS DOES *NOT* PROVE.  It does NOT establish the full no-fault candidate class `Cand_N`, nor
   `StateWF`.  Those additionally require:
     - relabelling the first/replay occurrences to `execPhase = once`;
     - GENERATING the successful normal PMP checks (they do not exist in the fault run);
     - REGENERATING the normal `ctx` chronology;
     - REBUILDING the state chain — note the no-fault initial PMP state is already repaired, so the
       fault run's copied pre/post states do NOT form a valid no-fault chain.
   That operational realization is the real bulk of general Stage-2 and is NOT done here.

   THEREFORE the honest reading of `general_ctx_erasure` is:
       "every fault candidate admits a trap-free RVWMO-consistent memory KERNEL with the same
        memory projection"
   and NOT "there exists a no-fault execution".

   Reuses the EXISTING abstract relations (no re-definition): `Clift_coherence.Cf` / `co_flt` /
   `fr_flt` / `coOn` / `inE0` instantiated at the two carriers, and `Obs_final_state.co_max_of`.
   0 Admitted / 0 axioms (`Print Assumptions general_ctx_erasure`).  Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Obs_final_state.
Import ListNotations.

Section CtxErasure.

  Variable Event Byte : Type.
  Variable gmo po poloc : Event -> Event -> Prop.
  Variable is_read is_write : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable E : list Event.           (* the contracted carrier X_C coming out of Stage 1 *)
  Variable Ctx : Event -> Prop.      (* the trap region: trap entry, handler body, CSR accesses, mret *)
  Variable ctx_dec : forall e, {Ctx e} + {~ Ctx e}.

  (* (1) THE `Hschema` CONSEQUENCE.  See the header: this is a consequence of the already-frozen
         handler schema, NOT a new contract commitment; but `Hschema` is unmechanized here, so this
         is a NAMED ANTECEDENT. *)
  Hypothesis ctx_silent :
    forall e, Ctx e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b).

  (* (2) interface facts about po-loc / rf — true of any RVWMO event structure, not new commitments. *)
  Hypothesis poloc_touches : forall x y, poloc x y -> exists b, touches x b /\ touches y b.
  Hypothesis rf_src_write  : forall w b r, rf w b r -> is_write w.
  (* EXTRA, beyond the commissioned interface — flagged in the header and in the report.
     Needed ONLY by `ctx_not_in_Cf` (rf disjunct, target endpoint).  Basic typing fact. *)
  Hypothesis rf_tgt_read   : forall w b r, rf w b r -> is_read r.

  (* The erased ("kernel") carrier. *)
  Definition EK : list Event := filter (fun e => if ctx_dec e then false else true) E.

  (* ===================================================================== *)
  (* 1.  EK basics                                                          *)
  (* ===================================================================== *)

  Lemma In_EK_iff : forall e, In e EK <-> (In e E /\ ~ Ctx e).
  Proof.
    intros e. unfold EK. rewrite filter_In. split.
    - intros [Hin Hb]. split; [exact Hin|].
      destruct (ctx_dec e) as [Hc|Hnc]; [discriminate Hb | exact Hnc].
    - intros [Hin Hnc]. split; [exact Hin|].
      destruct (ctx_dec e) as [Hc|_]; [exfalso; apply Hnc; exact Hc | reflexivity].
  Qed.

  Lemma EK_sub : forall e, In e EK -> In e E.
  Proof. intros e H. apply In_EK_iff in H. destruct H as [H _]; exact H. Qed.

  Lemma EK_trap_free : forall e, In e EK -> ~ Ctx e.
  Proof. intros e H. apply In_EK_iff in H. destruct H as [_ H]; exact H. Qed.

  (* Silence, contrapositively: an RVWMO-relevant event cannot be in the trap region. *)
  Lemma write_not_ctx : forall e, is_write e -> ~ Ctx e.
  Proof.
    intros e Hw Hc. destruct (ctx_silent e Hc) as [_ [Hnw _]]. exact (Hnw Hw).
  Qed.

  Lemma read_not_ctx : forall e, is_read e -> ~ Ctx e.
  Proof.
    intros e Hr Hc. destruct (ctx_silent e Hc) as [Hnr _]. exact (Hnr Hr).
  Qed.

  Lemma touch_not_ctx : forall e b, touches e b -> ~ Ctx e.
  Proof.
    intros e b Ht Hc. destruct (ctx_silent e Hc) as [_ [_ Hnt]]. exact (Hnt b Ht).
  Qed.

  (* THE CRUX, packaged: no WRITE is erased. *)
  Lemma write_in_EK : forall e, In e E -> is_write e -> In e EK.
  Proof.
    intros e Hin Hw. apply In_EK_iff. split; [exact Hin | apply write_not_ctx; exact Hw].
  Qed.

  (* ===================================================================== *)
  (* 2.  The trap region touches no per-location edge at all                *)
  (* ===================================================================== *)

  Definition CfE  := Clift_coherence.Cf Event Byte gmo is_write is_read touches E  rf poloc.
  Definition CfEK := Clift_coherence.Cf Event Byte gmo is_write is_read touches EK rf poloc.

  (* NOTE: this lemma (and only this lemma) uses the extra `rf_tgt_read` hypothesis. *)
  Theorem ctx_not_in_Cf : forall x y, CfE x y -> ~ Ctx x /\ ~ Ctx y.
  Proof.
    intros x y H. unfold CfE, Clift_coherence.Cf in H.
    destruct H as [[b Hco] | [ [b [Hrx Hfr]] | [ [b Hrf] | Hpl ] ] ].
    - (* co: both endpoints are writes *)
      unfold Clift_coherence.co_flt, Clift_coherence.coOn in Hco.
      destruct Hco as [_ [_ [Wx [Wy _]]]].
      split; apply write_not_ctx; assumption.
    - (* fr: x is a read (from the disjunct), y is a write (from the inner co_flt) *)
      unfold Clift_coherence.fr_flt in Hfr. destruct Hfr as [w1 [_ Hco]].
      unfold Clift_coherence.co_flt, Clift_coherence.coOn in Hco.
      destruct Hco as [_ [_ [_ [Wy _]]]].
      split; [apply read_not_ctx; exact Hrx | apply write_not_ctx; exact Wy].
    - (* rf: x is a write (rf_src_write), y is a read (rf_tgt_read — the EXTRA hypothesis) *)
      split.
      + apply write_not_ctx. exact (rf_src_write x b y Hrf).
      + apply read_not_ctx.  exact (rf_tgt_read  x b y Hrf).
    - (* po-loc: both endpoints touch a common byte *)
      destruct (poloc_touches x y Hpl) as [b [Tx Ty]].
      split; [apply (touch_not_ctx x b Tx) | apply (touch_not_ctx y b Ty)].
  Qed.

  (* ===================================================================== *)
  (* 3.  co_flt / fr_flt are carrier-insensitive to erasing Ctx             *)
  (*     (because no write is erased — `write_in_EK`)                       *)
  (* ===================================================================== *)

  Lemma co_flt_EK_iff : forall b w1 w2,
    Clift_coherence.co_flt Event Byte gmo is_write touches E  b w1 w2 <->
    Clift_coherence.co_flt Event Byte gmo is_write touches EK b w1 w2.
  Proof.
    intros b w1 w2.
    unfold Clift_coherence.co_flt, Clift_coherence.coOn, Clift_coherence.inE0.
    split.
    - intros [I1 [I2 [W1 [W2 [T1 [T2 G]]]]]].
      repeat split; try assumption; apply write_in_EK; assumption.
    - intros [I1 [I2 [W1 [W2 [T1 [T2 G]]]]]].
      repeat split; try assumption; apply EK_sub; assumption.
  Qed.

  Lemma fr_flt_EK_iff : forall b r w2,
    Clift_coherence.fr_flt Event Byte gmo is_write touches E  rf b r w2 <->
    Clift_coherence.fr_flt Event Byte gmo is_write touches EK rf b r w2.
  Proof.
    intros b r w2. unfold Clift_coherence.fr_flt. split.
    - intros [w1 [Hrf Hco]]. exists w1. split; [exact Hrf|]. apply co_flt_EK_iff; exact Hco.
    - intros [w1 [Hrf Hco]]. exists w1. split; [exact Hrf|]. apply co_flt_EK_iff; exact Hco.
  Qed.

  (* ===================================================================== *)
  (* 4.  The two per-location relations COINCIDE                            *)
  (* ===================================================================== *)

  Theorem Cf_EK_iff : forall x y, CfEK x y <-> CfE x y.
  Proof.
    intros x y. unfold CfEK, CfE, Clift_coherence.Cf. split.
    - intros [[b Hco] | [ [b [Hrx Hfr]] | [ [b Hrf] | Hpl ] ] ].
      + left. exists b. apply co_flt_EK_iff; exact Hco.
      + right; left. exists b. split; [exact Hrx|]. apply fr_flt_EK_iff; exact Hfr.
      + right; right; left. exists b. exact Hrf.
      + right; right; right. exact Hpl.
    - intros [[b Hco] | [ [b [Hrx Hfr]] | [ [b Hrf] | Hpl ] ] ].
      + left. exists b. apply co_flt_EK_iff; exact Hco.
      + right; left. exists b. split; [exact Hrx|]. apply fr_flt_EK_iff; exact Hfr.
      + right; right; left. exists b. exact Hrf.
      + right; right; right. exact Hpl.
  Qed.

  (* ===================================================================== *)
  (* 5.  Acyclicity transfers                                               *)
  (* ===================================================================== *)

  Lemma ct_mono : forall x y, clos_trans Event CfEK x y -> clos_trans Event CfE x y.
  Proof.
    intros x y H. induction H as [x y Hstep | x y z _ IH1 _ IH2].
    - apply t_step. apply Cf_EK_iff; exact Hstep.
    - exact (t_trans Event CfE x y z IH1 IH2).
  Qed.

  Theorem erase_ctx_perloc_acyclic :
    (forall x, ~ clos_trans Event CfE x x) -> (forall x, ~ clos_trans Event CfEK x x).
  Proof.
    intros Hacyc x Hcyc. apply (Hacyc x). apply ct_mono; exact Hcyc.
  Qed.

  (* ===================================================================== *)
  (* 6.  store_between / r2 are UNAFFECTED — the obstruction never arises   *)
  (* ===================================================================== *)

  Definition store_between_on (C : Event -> Prop) (b : Byte) (a c : Event) : Prop :=
    exists w, C w /\ is_write w /\ touches w b /\ po a w /\ po w c.

  (* This is the "intervening-store reflection" property.  It is the load-bearing point of the whole
     design: the intervening witness `w` is a WRITE, so by `ctx_silent` it is not in `Ctx`, so it
     SURVIVES the erasure.  Hence erasing `Ctx` can never DESTROY a `store_between` witness, i.e. it
     can never turn a "there is an intervening store" pair into a `polnw` (po-loc no-write-between)
     pair, i.e. it can never CREATE an r2 edge.  Contrast deleting a *write* (Stage 1), where exactly
     this can happen and forces the whole r2 anti-monotonicity argument.  Here it is vacuous. *)
  Theorem ctx_erasure_store_between_reflect : forall b a c,
    store_between_on (fun e => In e E)  b a c <->
    store_between_on (fun e => In e EK) b a c.
  Proof.
    intros b a c. unfold store_between_on. split.
    - intros [w [Hin [Hw [Ht [P1 P2]]]]].
      exists w. repeat split; try assumption. apply write_in_EK; assumption.
    - intros [w [Hin [Hw [Ht [P1 P2]]]]].
      exists w. repeat split; try assumption. apply EK_sub; assumption.
  Qed.

  (* ===================================================================== *)
  (* 7.  Memory projection preserved                                        *)
  (* ===================================================================== *)

  Theorem erase_ctx_preserves_co_max : forall b w,
    Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E)  b w <->
    Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e EK) b w.
  Proof.
    intros b w. unfold Obs_final_state.co_max_of. split.
    - intros [Hw [Ht [Hin Hmax]]].
      repeat split; try assumption.
      + apply write_in_EK; assumption.
      + intros w' Hin' Hw' Ht'. apply Hmax; [apply EK_sub; exact Hin' | exact Hw' | exact Ht'].
    - intros [Hw [Ht [Hin Hmax]]].
      repeat split; try assumption.
      + apply EK_sub; exact Hin.
      + intros w' Hin' Hw' Ht'.
        apply Hmax; [apply write_in_EK; assumption | exact Hw' | exact Ht'].
  Qed.

  (* rf sources are writes, hence survive: no read of the kernel is left sourceless. *)
  Theorem erase_ctx_preserves_rf : forall w b r,
    rf w b r -> In r E -> ~ Ctx r -> (In w EK <-> In w E).
  Proof.
    intros w b r Hrf _ _. split.
    - apply EK_sub.
    - intros Hin. apply write_in_EK; [exact Hin | exact (rf_src_write w b r Hrf)].
  Qed.

  (* ===================================================================== *)
  (* 8.  HEADLINE                                                           *)
  (* ===================================================================== *)

  (* Honest reading (see header): every fault candidate admits a trap-free RVWMO-consistent memory
     KERNEL with the same memory projection.  NOT: "there exists a no-fault execution". *)
  Theorem general_ctx_erasure :
    (* the erased carrier is trap-free *)
    (forall e, In e EK -> ~ Ctx e)
    (* the two per-location relations are THE SAME relation *)
    /\ (forall x y, CfEK x y <-> CfE x y)
    (* hence per-location consistency transfers *)
    /\ ((forall x, ~ clos_trans Event CfE x x) -> (forall x, ~ clos_trans Event CfEK x x))
    (* the r2 hazard is absent: intervening stores reflect in both directions *)
    /\ (forall b a c, store_between_on (fun e => In e E)  b a c
                  <-> store_between_on (fun e => In e EK) b a c)
    (* memory projection unchanged, byte by byte *)
    /\ (forall b w,
          Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E)  b w <->
          Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e EK) b w).
  Proof.
    split; [ exact EK_trap_free | ].
    split; [ intros u v; apply Cf_EK_iff | ].
    split; [ exact erase_ctx_perloc_acyclic | ].
    split; [ intros b a c; apply ctx_erasure_store_between_reflect | ].
    intros b w. apply erase_ctx_preserves_co_max.
  Qed.

End CtxErasure.
