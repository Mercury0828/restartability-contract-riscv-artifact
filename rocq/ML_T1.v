(* ML_T1.v — RESTART-V: the refinement theorem for ANY finite set of provisionally written lanes.

   `T1_frozen_refinement.frozen_T1_refinement` erases one duplicate pair (k, d). Here the fault run
   carries a finite list LS of pairs, one per lane written before the fault, and every replay duplicate
   is erased at once (carrier `ML_base.carrier_L`, reads-from `ML_base.rf_L`). The conclusion has the
   same five parts as the one-lane theorem:

     (i)   the witness passes the per-location check  acyclic(co ∪ rf ∪ fr ∪ po-loc);
     (ii)  the witness passes the main-model check     acyclic(co ∪ rfe ∪ fr ∪ ppo), with the frozen
           preserved-program-order rules discharged (no `ppo_lifts` premise);
     (iii) the witness satisfies the C4 load-value rule over its carrier;
     (iv)  every retained read keeps its byte value;
     (v)   every byte's coherence-latest written value is preserved.

   The fault-run antecedents are LITERALLY the one-lane theorem's: acyclicity of
   `Clift_coherence.Cf` and of `Frozen_mainmodel.FRf` over E0. Each lane carries the one-lane pair
   premises (record `LaneOK`); the only cross-lane premise is that no keeper is itself deleted.

   Why the one-lane proof generalizes edge by edge. Every witness edge is lifted to a fault-run path
   exactly as in Clift_coherence / Rlift_mainmodel / PPO_union. A reads-from, from-reads or r12 edge
   involves ONE source write, hence at most one lane; a retargeted edge lifts through that lane's
   k ->co d. The erasure condition is the per-byte γ_adj of each lane: no write to a byte d touches
   lies coherence-between k and d. Writes of OTHER lanes touch other bytes, so in the natural run
   (all first attempts, trap, all replays) they do not violate it.

   `ML_T1_covers_single_lane` shows the one-lane premises imply this theorem's premises at LS = [(k,d)],
   with the same carrier and the same reads-from, so the general statement contains the frozen one.
   `ML_T1_refinement_instantiated` replaces the per-lane po-twin / r12 premises by the token-level
   commitments of Token_model, lane by lane.

   0 Admitted / 0 axioms (Print Assumptions). No existing .v file is modified. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import RestartV.L2_ppo.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Obs_final_state.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Rlift_mainmodel.
Require Import RestartV.PPO_union.
Require Import RestartV.Frozen_mainmodel.
Require Import RestartV.Token_model.
Require Import RestartV.ML_base.
Import ListNotations.

Section MLT1.

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
  Variable LS : list (Event * Event).

  (* ------------------------------------------------------------------ the general carrier *)

  Definition isdelL (x : Event) : Prop := ML_base.isdel Event LS x.
  Definition survL (x : Event) : Prop := ML_base.survivor_L Event E0 LS x.
  Definition E_L : list Event := ML_base.carrier_L Event eq_ev_dec E0 LS.
  Definition rfL : Event -> Byte -> Event -> Prop := ML_base.rf_L Event LS Byte rf.

  (* ------------------------------------------------------------------ the fault-run relations *)

  Definition CfF : Event -> Event -> Prop :=
    Clift_coherence.Cf Event Byte gmo is_write is_read touches E0 rf poloc.
  Definition FRfF : Event -> Event -> Prop :=
    Frozen_mainmodel.FRf Event Byte Hart gmo is_write is_read is_load is_store touches
      same_addr addr data ctrl fence hart E0 rf po.

  (* ------------------------------------------------------------------ the witness relations *)

  Definition co_L (b : Byte) (w1 w2 : Event) : Prop :=
    survL w1 /\ survL w2 /\ is_write w1 /\ is_write w2 /\ touches w1 b /\ touches w2 b /\ gmo w1 w2.
  Definition fr_L (b : Byte) (r w2 : Event) : Prop := exists w1, rfL w1 b r /\ co_L b w1 w2.
  Definition rfe_L (x y : Event) : Prop :=
    exists b, survL x /\ survL y /\ rfL x b y /\ hart x <> hart y.

  (* the witness per-location relation, carrier-restricted on every disjunct *)
  Definition Cn_L (x y : Event) : Prop :=
    (exists b, co_L b x y) \/
    (exists b, survL x /\ survL y /\ is_read x /\ fr_L b x y) \/
    (exists b, survL x /\ survL y /\ rfL x b y) \/
    (poloc x y /\ survL x /\ survL y).

  (* the witness frozen PPO: PPO_union.ppo_wit with the general survivor set and reads-from *)
  Definition store_between_NL (x : Byte) (a b : Event) : Prop :=
    exists w, survL w /\ is_write w /\ touches w x /\ po a w /\ po w b.
  Definition polnw_NL (x : Byte) (a b : Event) : Prop :=
    is_read a /\ is_read b /\ touches a x /\ touches b x /\ po a b /\
    survL a /\ survL b /\ ~ store_between_NL x a b.
  Definition rsw_NL (x : Byte) (a b : Event) : Prop := exists w, rfL w x a /\ rfL w x b.
  Definition r2NL (x : Byte) (a b : Event) : Prop := polnw_NL x a b /\ ~ rsw_NL x a b.

  Inductive ppo_wit_L : Event -> Event -> Prop :=
  | pl1  : forall a b, survL a -> survL b -> po a b -> same_addr a b -> is_store b -> ppo_wit_L a b
  | pl4  : forall a b, survL a -> survL b -> fence a b -> ppo_wit_L a b
  | pl9  : forall a b, survL a -> survL b -> addr a b -> ppo_wit_L a b
  | pl10 : forall a b, survL a -> survL b -> data a b -> ppo_wit_L a b
  | pl11 : forall a b, survL a -> survL b -> ctrl a b -> is_store b -> ppo_wit_L a b
  | pl13 : forall a b, survL a -> survL b -> is_store b ->
             (exists m, survL m /\ po a m /\ po m b /\ addr a m) -> ppo_wit_L a b
  | pl12 : forall a b, survL a -> survL b -> is_load b ->
             (exists m bb, po a m /\ po m b /\ (addr a m \/ data a m) /\ rfL m bb b) -> ppo_wit_L a b
  | pl2  : forall x a b, r2NL x a b -> ppo_wit_L a b.

  (* the witness main-model relation, carrier-restricted on every disjunct *)
  Definition Rn_L (x y : Event) : Prop :=
    (exists b, co_L b x y) \/
    (exists b, survL x /\ survL y /\ is_read x /\ fr_L b x y) \/
    rfe_L x y \/
    ppo_wit_L x y.

  (* ------------------------------------------------------------------ premises *)

  (* coherence well-formedness over the fault carrier; program order transitive *)
  Hypothesis Hirr : forall e, In e E0 -> ~ gmo e e.
  Hypothesis Htr  : forall a b c, In a E0 -> In b E0 -> In c E0 -> gmo a b -> gmo b c -> gmo a c.
  Hypothesis Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.
  Hypothesis Hpo_trans : forall a b c, po a b -> po b c -> po a c.

  (* the RVWMO interface of the fault run *)
  Hypothesis rf_is_C4 : forall b r w, is_read r -> In r E0 -> rf w b r ->
      L1_abstract_erasure.C4_source Event Byte is_write touches gmo po E0 b r w.
  Hypothesis rf_touches : forall w b r, rf w b r -> touches w b.
  Hypothesis rf_functional : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.

  (* what each lane (k = first attempt, d = replay) must satisfy: the one-lane pair premises *)
  Record LaneOK (k d : Event) : Prop := {
    lk_in   : In k E0;
    ld_in   : In d E0;
    lk_w    : is_write k;
    ld_w    : is_write d;
    l_gmo   : gmo k d;                               (* keeper coherence-before the replay *)
    l_po    : po k d;                                (* re-execution orientation *)
    l_hart  : hart d = hart k;
    l_foot  : forall b, touches d b -> touches k b;
    l_val   : forall b, touches d b -> wval k b = wval d b;
    l_adj   : forall b, touches d b ->               (* γ_adj, per byte *)
                forall w, In w E0 -> is_write w -> touches w b -> ~ (gmo k w /\ gmo w d);
    l_twin  : forall a c x, is_read a -> touches a x -> touches d x -> po a d -> po d c ->
                po a k /\ po k c;
    l_r12   : forall a c bb, po a k -> po k c -> (addr a k \/ data a k) -> rf d bb c ->
                po a d /\ po d c /\ (addr a d \/ data a d)
  }.

  Hypothesis Hlanes : forall k d, In (k, d) LS -> LaneOK k d.
  (* the only cross-lane premise: a keeper is never itself a deleted duplicate *)
  Hypothesis keeper_survives : forall k d, In (k, d) LS -> ~ isdelL k.

  (* ------------------------------------------------------------------ carrier facts *)

  Lemma survL_in : forall x, survL x -> In x E0.
  Proof. intros x [H _]; exact H. Qed.

  Lemma survL_E_L : forall x, In x E_L <-> survL x.
  Proof. intro x. exact (ML_base.survivor_carrier Event eq_ev_dec E0 LS x). Qed.

  Lemma del_lane : forall d, isdelL d -> exists k, In (k, d) LS.
  Proof. intros d H. exact (proj1 (ML_base.isdel_lane Event LS d) H). Qed.

  Lemma lane_isdel : forall k d, In (k, d) LS -> isdelL d.
  Proof. intros k d H. exact (ML_base.lane_del Event LS k d H). Qed.

  Lemma keeper_surv : forall k d, In (k, d) LS -> survL k.
  Proof.
    intros k d H. split; [exact (lk_in _ _ (Hlanes k d H)) | exact (keeper_survives k d H)].
  Qed.

  Lemma surv_not_lane_del : forall k d w, In (k, d) LS -> survL w -> w <> d.
  Proof.
    intros k d w H [_ Hw] E. subst w. apply Hw. exact (lane_isdel k d H).
  Qed.

  (* a retained source is either an undeleted write or a lane keeper standing in for its replay *)
  Lemma rfL_cases : forall w b r,
      rfL w b r -> (rf w b r /\ ~ isdelL w) \/ (exists d, In (w, d) LS /\ rf d b r).
  Proof.
    intros w b r [[H N] | H].
    - left. split; [exact H |]. intro D. apply N. exists w. split; [exact D | exact H].
    - right; exact H.
  Qed.

  (* the γ_adj crux: a survivor coherence-after a lane's keeper, at a byte the replay touches, is
     coherence-after the replay too *)
  Lemma adj_crux : forall k d b w2,
      In (k, d) LS -> touches d b -> survL w2 -> is_write w2 -> touches w2 b -> gmo k w2 ->
      gmo d w2.
  Proof.
    intros k d b w2 Hl Tdb Sw2 Ww2 Tw2 Gkw2.
    pose proof (Hlanes k d Hl) as L.
    assert (Hne : d <> w2) by (intro E; exact (surv_not_lane_del k d w2 Hl Sw2 (eq_sym E))).
    destruct (Htot d w2 (ld_in _ _ L) (survL_in w2 Sw2) Hne) as [G | G]; [exact G |].
    exfalso. apply (l_adj _ _ L b Tdb w2 (survL_in w2 Sw2) Ww2 Tw2). split; [exact Gkw2 | exact G].
  Qed.

  (* ------------------------------------------------------------------ fault-edge constructors *)

  Lemma Cf_co : forall b w1 w2, In w1 E0 -> In w2 E0 -> is_write w1 -> is_write w2 ->
      touches w1 b -> touches w2 b -> gmo w1 w2 -> CfF w1 w2.
  Proof.
    intros. unfold CfF, Clift_coherence.Cf. left. exists b.
    unfold Clift_coherence.co_flt, Clift_coherence.coOn, Clift_coherence.inE0.
    repeat split; assumption.
  Qed.

  Lemma Cf_fr : forall b r w1 w2, is_read r -> rf w1 b r -> In w1 E0 -> In w2 E0 ->
      is_write w1 -> is_write w2 -> touches w1 b -> touches w2 b -> gmo w1 w2 -> CfF r w2.
  Proof.
    intros. unfold CfF, Clift_coherence.Cf. right. left. exists b. split; [assumption |].
    unfold Clift_coherence.fr_flt. exists w1. split; [assumption |].
    unfold Clift_coherence.co_flt, Clift_coherence.coOn, Clift_coherence.inE0.
    repeat split; assumption.
  Qed.

  Lemma Cf_rf : forall b w r, rf w b r -> CfF w r.
  Proof. intros. unfold CfF, Clift_coherence.Cf. right. right. left. exists b. assumption. Qed.

  Lemma Cf_poloc : forall x y, poloc x y -> CfF x y.
  Proof. intros. unfold CfF, Clift_coherence.Cf. right. right. right. assumption. Qed.

  Lemma FRf_co : forall b w1 w2, In w1 E0 -> In w2 E0 -> is_write w1 -> is_write w2 ->
      touches w1 b -> touches w2 b -> gmo w1 w2 -> FRfF w1 w2.
  Proof.
    intros. unfold FRfF, Frozen_mainmodel.FRf, Rlift_mainmodel.Rf. left. exists b.
    unfold Rlift_mainmodel.co_flt, Rlift_mainmodel.coOn, Rlift_mainmodel.inE0.
    repeat split; assumption.
  Qed.

  Lemma FRf_fr : forall b r w1 w2, is_read r -> rf w1 b r -> In w1 E0 -> In w2 E0 ->
      is_write w1 -> is_write w2 -> touches w1 b -> touches w2 b -> gmo w1 w2 -> FRfF r w2.
  Proof.
    intros. unfold FRfF, Frozen_mainmodel.FRf, Rlift_mainmodel.Rf. right. left. exists b.
    split; [assumption |].
    unfold Rlift_mainmodel.fr_flt. exists w1. split; [assumption |].
    unfold Rlift_mainmodel.co_flt, Rlift_mainmodel.coOn, Rlift_mainmodel.inE0.
    repeat split; assumption.
  Qed.

  Lemma FRf_rfe : forall b w r, rf w b r -> hart w <> hart r -> FRfF w r.
  Proof.
    intros. unfold FRfF, Frozen_mainmodel.FRf, Rlift_mainmodel.Rf. right. right. left.
    unfold Rlift_mainmodel.rfe_flt. exists b. split; assumption.
  Qed.

  Lemma FRf_ppoF : forall x y,
      PPO_union.ppoF Event Byte po is_load is_store same_addr addr data ctrl fence rf x y ->
      FRfF x y.
  Proof.
    intros. unfold FRfF, Frozen_mainmodel.FRf, Rlift_mainmodel.Rf. right. right. right.
    unfold Frozen_mainmodel.fault_ppo. left. assumption.
  Qed.

  Lemma FRf_r2F : forall bx x y,
      PPO_union.r2F Event Byte po is_read is_write touches rf E0 bx x y -> FRfF x y.
  Proof.
    intros. unfold FRfF, Frozen_mainmodel.FRf, Rlift_mainmodel.Rf. right. right. right.
    unfold Frozen_mainmodel.fault_ppo. right. exists bx. assumption.
  Qed.

  (* ------------------------------------------------------------------ (i) per-location lift *)

  Lemma Cn_L_lifts : forall x y, Cn_L x y -> clos_trans Event CfF x y.
  Proof.
    intros x y H.
    destruct H as [[b Hco] | [[b [Sx [Sy [Rx Hfr]]]] | [[b [Sx [Sy Hrf]]] | [Hpl _]]]].
    - destruct Hco as [S1 [S2 [W1 [W2 [T1 [T2 G]]]]]].
      apply t_step. apply (Cf_co b); auto using survL_in.
    - destruct Hfr as [w1 [Hrf1 Hco]].
      destruct Hco as [S1 [S2 [W1 [W2 [T1 [T2 G]]]]]].
      apply t_step.
      destruct (rfL_cases w1 b x Hrf1) as [[Hr _] | [d [Hl Hrd]]].
      + apply (Cf_fr b x w1 y); auto using survL_in.
      + pose proof (Hlanes w1 d Hl) as L.
        assert (Tdb : touches d b) by exact (rf_touches d b x Hrd).
        apply (Cf_fr b x d y); auto using survL_in.
        * exact (ld_in _ _ L).
        * exact (ld_w _ _ L).
        * exact (adj_crux w1 d b y Hl Tdb S2 W2 T2 G).
    - destruct (rfL_cases x b y Hrf) as [[Hr _] | [d [Hl Hrd]]].
      + apply t_step. exact (Cf_rf b x y Hr).
      + (* retargeted keeper -> read lifts to the two-edge path  k ->co d ->rf r *)
        pose proof (Hlanes x d Hl) as L.
        assert (Tdb : touches d b) by exact (rf_touches d b y Hrd).
        apply (t_trans Event CfF x d y).
        * apply t_step. apply (Cf_co b x d (lk_in _ _ L) (ld_in _ _ L) (lk_w _ _ L) (ld_w _ _ L)
                                   (l_foot _ _ L b Tdb) Tdb (l_gmo _ _ L)).
        * apply t_step. exact (Cf_rf b d y Hrd).
    - apply t_step. exact (Cf_poloc x y Hpl).
  Qed.

  Theorem ML_witness_perloc_acyclic :
    (forall x, ~ clos_trans Event CfF x x) -> forall x, ~ clos_trans Event Cn_L x x.
  Proof.
    intro Hacyc. apply (acyclic_via_simulation Event CfF Cn_L); [exact Cn_L_lifts | exact Hacyc].
  Qed.

  (* ------------------------------------------------------------------ (ii) main-model lift *)

  (* r2: deleting writes cannot create a po-loc-no-write pair (each deleted replay has a surviving
     twin at the same program-order cut), and retargeting can only merge sources *)
  Lemma r2NL_sub_r2F : forall x a b,
      r2NL x a b -> PPO_union.r2F Event Byte po is_read is_write touches rf E0 x a b.
  Proof.
    intros x a b [[Ra [Rb [Tax [Tbx [Pab [Sa [Sb Hnb]]]]]]] Hn].
    unfold PPO_union.r2F, PPO_union.polnw_F, PPO_union.store_between_F, PPO_union.rsw_F.
    split.
    - split; [exact Ra |]. split; [exact Rb |]. split; [exact Tax |]. split; [exact Tbx |].
      split; [exact Pab |].
      intros [w [Inw [Ww [Twx [Paw Pwb]]]]]. apply Hnb.
      destruct (ML_base.isdel_dec Event eq_ev_dec LS w) as [D | N].
      + destruct (del_lane w D) as [k Hl]. pose proof (Hlanes k w Hl) as L.
        destruct (l_twin _ _ L a b x Ra Tax Twx Paw Pwb) as [Pak Pkb].
        exists k. split; [exact (keeper_surv k w Hl) |].
        split; [exact (lk_w _ _ L) |]. split; [exact (l_foot _ _ L x Twx) |].
        split; [exact Pak | exact Pkb].
      + exists w. split; [split; [exact Inw | exact N] |].
        split; [exact Ww |]. split; [exact Twx |]. split; [exact Paw | exact Pwb].
    - intros [w [Rwa Rwb]]. apply Hn.
      destruct (ML_base.isdel_dec Event eq_ev_dec LS w) as [D | N].
      + destruct (del_lane w D) as [k Hl]. exists k.
        split; right; exists w; split; assumption.
      + exists w. split; left; (split; [assumption |]); intros [d [Dd Hrd]]; apply N.
        * rewrite (rf_functional w d x a Rwa Hrd). exact Dd.
        * rewrite (rf_functional w d x b Rwb Hrd). exact Dd.
  Qed.

  Lemma ppo_wit_L_lifts : forall x y, ppo_wit_L x y -> FRfF x y.
  Proof.
    intros x y H. destruct H.
    - apply FRf_ppoF. apply PPO_union.fr1; assumption.
    - apply FRf_ppoF. apply PPO_union.fr4; assumption.
    - apply FRf_ppoF. apply PPO_union.fr9; assumption.
    - apply FRf_ppoF. apply PPO_union.fr10; assumption.
    - apply FRf_ppoF. apply PPO_union.fr11; assumption.
    - apply FRf_ppoF. apply PPO_union.fr13; [assumption |].
      destruct H2 as [m [_ [Pam [Pmb Aam]]]]. exists m. auto.
    - apply FRf_ppoF. apply PPO_union.fr12; [assumption |].
      destruct H2 as [m [bb [Pam [Pmb [Hdep Hrf]]]]].
      destruct (rfL_cases m bb b Hrf) as [[Hr _] | [d [Hl Hrd]]].
      + exists m, bb. auto.
      + pose proof (Hlanes m d Hl) as L.
        destruct (l_r12 _ _ L a b bb Pam Pmb Hdep Hrd) as [Pad [Pdb Hdepd]].
        exists d, bb. auto.
    - apply (FRf_r2F x). apply r2NL_sub_r2F; exact H.
  Qed.

  Lemma Rn_L_lifts : forall x y, Rn_L x y -> clos_trans Event FRfF x y.
  Proof.
    intros x y H.
    destruct H as [[b Hco] | [[b [Sx [Sy [Rx Hfr]]]] | [Hrfe | Hpp]]].
    - destruct Hco as [S1 [S2 [W1 [W2 [T1 [T2 G]]]]]].
      apply t_step. apply (FRf_co b); auto using survL_in.
    - destruct Hfr as [w1 [Hrf1 Hco]].
      destruct Hco as [S1 [S2 [W1 [W2 [T1 [T2 G]]]]]].
      apply t_step.
      destruct (rfL_cases w1 b x Hrf1) as [[Hr _] | [d [Hl Hrd]]].
      + apply (FRf_fr b x w1 y); auto using survL_in.
      + pose proof (Hlanes w1 d Hl) as L.
        assert (Tdb : touches d b) by exact (rf_touches d b x Hrd).
        apply (FRf_fr b x d y); auto using survL_in.
        * exact (ld_in _ _ L).
        * exact (ld_w _ _ L).
        * exact (adj_crux w1 d b y Hl Tdb S2 W2 T2 G).
    - destruct Hrfe as [b [Sx [Sy [Hrf Hext]]]].
      destruct (rfL_cases x b y Hrf) as [[Hr _] | [d [Hl Hrd]]].
      + apply t_step. exact (FRf_rfe b x y Hr Hext).
      + (* retargeted keeper -> external read: k ->co d ->rfe r, same hart for k and d *)
        pose proof (Hlanes x d Hl) as L.
        assert (Tdb : touches d b) by exact (rf_touches d b y Hrd).
        apply (t_trans Event FRfF x d y).
        * apply t_step. apply (FRf_co b x d (lk_in _ _ L) (ld_in _ _ L) (lk_w _ _ L) (ld_w _ _ L)
                                    (l_foot _ _ L b Tdb) Tdb (l_gmo _ _ L)).
        * apply t_step. apply (FRf_rfe b d y Hrd). rewrite (l_hart _ _ L). exact Hext.
    - apply t_step. exact (ppo_wit_L_lifts x y Hpp).
  Qed.

  Theorem ML_witness_mainmodel_acyclic :
    (forall x, ~ clos_trans Event FRfF x x) -> forall x, ~ clos_trans Event Rn_L x x.
  Proof.
    intro Hacyc. apply (acyclic_via_simulation Event FRfF Rn_L); [exact Rn_L_lifts | exact Hacyc].
  Qed.

  (* ------------------------------------------------------------------ (iii) load-value rule *)

  Theorem ML_erasure_preserves_consistency :
    L1_abstract_erasure.L1_consistent Event Byte is_write is_read touches gmo po E_L rfL.
  Proof.
    assert (Hsub : forall e, In e E_L -> In e E0)
      by (intros e He; apply survL_in; apply survL_E_L; exact He).
    split.
    - split; [| split].
      + intros e He. apply Hirr. apply Hsub; exact He.
      + intros a b c Ha Hb Hc. apply Htr; apply Hsub; assumption.
      + intros a b Ha Hb. apply Htot; apply Hsub; assumption.
    - intros b r w Hr Hr_in Hrf.
      assert (Hr0 : In r E0) by (apply Hsub; exact Hr_in).
      unfold L1_abstract_erasure.C4_source, L1_abstract_erasure.cand.
      destruct (rfL_cases w b r Hrf) as [[Hw Nw] | [d [Hl Hrd]]].
      + (* source kept: still the C4 source over the smaller carrier *)
        destruct (rf_is_C4 b r w Hr Hr0 Hw) as [[Inw [Ww [Tw Ord]]] Hmax].
        split.
        * split; [apply survL_E_L; split; [exact Inw | exact Nw] |]. auto.
        * intros w' [Inw' Rest]. apply Hmax. split; [apply Hsub; exact Inw' | exact Rest].
      + (* source was a deleted replay d: its lane's keeper w takes its place *)
        pose proof (Hlanes w d Hl) as L.
        destruct (rf_is_C4 b r d Hr Hr0 Hrd) as [[Ind [Wd [Td Ord]]] Hmax].
        split.
        * split; [apply survL_E_L; exact (keeper_surv w d Hl) |].
          split; [exact (lk_w _ _ L) |]. split; [exact (l_foot _ _ L b Td) |].
          destruct Ord as [G | P].
          -- left. exact (Htr w d r (lk_in _ _ L) Ind Hr0 (l_gmo _ _ L) G).
          -- right. exact (Hpo_trans w d r (l_po _ _ L) P).
        * intros w' [Inw' [Ww' [Tw' Ord']]].
          assert (Sw' : survL w') by (apply survL_E_L; exact Inw').
          destruct (eq_ev_dec w' w) as [E | Nk]; [left; exact E | right].
          destruct (Hmax w' (conj (survL_in w' Sw') (conj Ww' (conj Tw' Ord')))) as [E | G'd].
          -- exfalso. exact (surv_not_lane_del w d w' Hl Sw' E).
          -- destruct (Htot w' w (survL_in w' Sw') (lk_in _ _ L) Nk) as [G | G]; [exact G |].
             exfalso. apply (l_adj _ _ L b Td w' (survL_in w' Sw') Ww' Tw'). split; assumption.
  Qed.

  (* ------------------------------------------------------------------ (iv) read values *)

  Theorem ML_erasure_preserves_read_values :
    forall r b w, rf w b r -> exists w', rfL w' b r /\ wval w' b = wval w b.
  Proof.
    intros r b w Hrf.
    destruct (ML_base.isdel_dec Event eq_ev_dec LS w) as [D | N].
    - destruct (del_lane w D) as [k Hl]. pose proof (Hlanes k w Hl) as L.
      exists k. split.
      + right. exists w. split; assumption.
      + exact (l_val _ _ L b (rf_touches w b r Hrf)).
    - exists w. split; [| reflexivity].
      left. split; [exact Hrf |]. intros [d [Dd Hrd]]. apply N.
      rewrite (rf_functional w d b r Hrf Hrd). exact Dd.
  Qed.

  (* ------------------------------------------------------------------ (v) final memory values *)

  Theorem ML_final_state_preserved_exists :
    forall b w_f,
      Obs_final_state.co_max_of Event Byte gmo is_write touches (Obs_final_state.inE0 Event E0) b w_f ->
      exists w_n, Obs_final_state.co_max_of Event Byte gmo is_write touches survL b w_n /\
                  wval w_f b = wval w_n b.
  Proof.
    intros b w_f [Wf [Tf [Inf Hmaxf]]].
    unfold Obs_final_state.co_max_of.
    destruct (ML_base.isdel_dec Event eq_ev_dec LS w_f) as [D | N].
    - (* the coherence-last write was a replay: its keeper is the new coherence-last survivor *)
      destruct (del_lane w_f D) as [k Hl]. pose proof (Hlanes k w_f Hl) as L.
      exists k. split.
      + split; [exact (lk_w _ _ L) |]. split; [exact (l_foot _ _ L b Tf) |].
        split; [exact (keeper_surv k w_f Hl) |].
        intros w' Sw' Ww' Tw'.
        destruct (eq_ev_dec w' k) as [E | Nk]; [left; exact E | right].
        destruct (Hmaxf w' (survL_in w' Sw') Ww' Tw') as [E | G].
        * exfalso. exact (surv_not_lane_del k w_f w' Hl Sw' E).
        * destruct (Htot w' k (survL_in w' Sw') (lk_in _ _ L) Nk) as [G' | G']; [exact G' |].
          exfalso. apply (l_adj _ _ L b Tf w' (survL_in w' Sw') Ww' Tw'). split; assumption.
      + symmetry. exact (l_val _ _ L b Tf).
    - exists w_f. split; [| reflexivity].
      split; [exact Wf |]. split; [exact Tf |]. split; [split; [exact Inf | exact N] |].
      intros w' Sw' Ww' Tw'. exact (Hmaxf w' (survL_in w' Sw') Ww' Tw').
  Qed.

  (* ------------------------------------------------------------------ the headline *)

  Theorem ML_T1_refinement :
    (forall x, ~ clos_trans Event
       (Clift_coherence.Cf Event Byte gmo is_write is_read touches E0 rf poloc) x x) ->
    (forall x, ~ clos_trans Event
       (Frozen_mainmodel.FRf Event Byte Hart gmo is_write is_read is_load is_store touches
          same_addr addr data ctrl fence hart E0 rf po) x x) ->
    exists (E_N : list Event) (rf_N : Event -> Byte -> Event -> Prop),
      E_N = ML_base.carrier_L Event eq_ev_dec E0 LS /\
      rf_N = ML_base.rf_L Event LS Byte rf /\
      (* (i)  per-location check of the witness *)
      (forall x, ~ clos_trans Event Cn_L x x) /\
      (* (ii) main-model check of the witness, frozen PPO discharged *)
      (forall x, ~ clos_trans Event Rn_L x x) /\
      (* (iii) C4 load-value rule of the witness over its carrier *)
      L1_abstract_erasure.L1_consistent Event Byte is_write is_read touches gmo po E_N rf_N /\
      (* (iv) every retained read keeps its byte value *)
      (forall r b w, In r E_N -> is_read r -> rf w b r ->
         exists w', rf_N w' b r /\ wval w' b = wval w b) /\
      (* (v)  every byte's coherence-latest written value is preserved *)
      (forall b w_f,
         Obs_final_state.co_max_of Event Byte gmo is_write touches (Obs_final_state.inE0 Event E0) b w_f ->
         exists w_n, Obs_final_state.co_max_of Event Byte gmo is_write touches
                       (ML_base.survivor_L Event E0 LS) b w_n /\
                     wval w_f b = wval w_n b).
  Proof.
    intros Hcf Hfrf.
    exists E_L, rfL.
    split; [reflexivity |]. split; [reflexivity |].
    split; [exact (ML_witness_perloc_acyclic Hcf) |].
    split; [exact (ML_witness_mainmodel_acyclic Hfrf) |].
    split; [exact ML_erasure_preserves_consistency |].
    split.
    - intros r b w _ _ Hrf. exact (ML_erasure_preserves_read_values r b w Hrf).
    - exact ML_final_state_preserved_exists.
  Qed.

End MLT1.

(* ==================================================================================================
   The one-lane theorem is the instance LS = [(k, d)]
   ================================================================================================== *)

Section SingleLane.

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

  Lemma single_carrier :
    ML_base.carrier_L Event eq_ev_dec E0 [(k, d)] =
    L1_abstract_erasure.contract_carrier Event eq_ev_dec E0 d.
  Proof.
    unfold ML_base.carrier_L, L1_abstract_erasure.contract_carrier.
    apply filter_pointwise. intro x.
    destruct (ML_base.isdel_dec Event eq_ev_dec [(k, d)] x) as [I | NI];
      destruct (eq_ev_dec x d) as [E | NE]; try reflexivity.
    - exfalso. unfold ML_base.isdel, ML_base.dels in I. simpl in I.
      destruct I as [I | []]. apply NE. symmetry. exact I.
    - exfalso. apply NI. unfold ML_base.isdel, ML_base.dels. simpl. left. symmetry. exact E.
  Qed.

  Lemma single_rf : forall w b r,
    ML_base.rf_L Event [(k, d)] Byte rf w b r <->
    L1_abstract_erasure.rf_retarget Event Byte d k rf w b r.
  Proof.
    intros w b r. unfold ML_base.rf_L, L1_abstract_erasure.rf_retarget, ML_base.isdel, ML_base.dels.
    simpl. split.
    - intros [[H N] | [d' [I H]]].
      + left. split; [exact H |]. intro Hd. apply N. exists d. split; [left; reflexivity | exact Hd].
      + right. destruct I as [I | []]. inversion I; subst. split; [exact H | reflexivity].
    - intros [[H N] | [H E]].
      + left. split; [exact H |]. intros [d' [[Dd | []] Hd']]. subst d'. contradiction.
      + right. exists d. subst w. split; [left; reflexivity | exact H].
  Qed.

  (* the frozen one-lane premises (T1_frozen_refinement's, verbatim) *)
  Hypothesis d_in : In d E0.
  Hypothesis d_w  : is_write d.
  Hypothesis k_in : In k E0.
  Hypothesis k_w  : is_write k.
  Hypothesis kd_ne : k <> d.
  Hypothesis keeper_before : gmo k d.
  Hypothesis Hro  : RO_K Event gmo po p q k.
  Hypothesis Hdpq : d = p \/ d = q.
  Hypothesis dup_val : forall b, touches d b -> wval k b = wval d b.
  Hypothesis hart_dk : hart d = hart k.
  Hypothesis Hadj : forall b, touches d b ->
      touches d b /\ touches k b /\
      (forall w, In w E0 -> is_write w -> touches w b -> ~ (gmo k w /\ gmo w d)).
  Hypothesis foot_dk : forall x, touches d x -> touches k x.
  Hypothesis po_twin : forall a b x,
    is_read a -> touches a x -> touches d x -> po a d -> po d b -> po a k /\ po k b.
  Hypothesis dup_r12 : forall a b bb,
      po a k -> po k b -> (addr a k \/ data a k) -> rf d bb b ->
      po a d /\ po d b /\ (addr a d \/ data a d).

  Lemma single_po_kd : po k d.
  Proof.
    destruct Hro as [[[Ek Gpq] | [Ek Gqp]] [Hp Hq]]; subst k;
      destruct Hdpq as [Ed | Ed]; subst d.
    - exfalso; apply kd_ne; reflexivity.
    - exact (Hp eq_refl).
    - exact (Hq eq_refl).
    - exfalso; apply kd_ne; reflexivity.
  Qed.

  Theorem ML_T1_covers_single_lane :
    (forall k' d', In (k', d') [(k, d)] ->
       LaneOK Event Byte Hart Value gmo is_write is_read touches wval addr data hart E0 rf po k' d') /\
    (forall k' d', In (k', d') [(k, d)] -> ~ ML_base.isdel Event [(k, d)] k').
  Proof.
    split.
    - intros k' d' [I | []]. inversion I; subst k' d'.
      constructor; try assumption.
      + exact single_po_kd.
      + intros b Tdb. exact (proj2 (proj2 (Hadj b Tdb))).
    - intros k' d' [I | []]. inversion I; subst k' d'.
      unfold ML_base.isdel, ML_base.dels. simpl. intros [E | []]. apply kd_ne. symmetry. exact E.
  Qed.

End SingleLane.

(* ==================================================================================================
   Token-level instantiation, lane by lane (the multi-lane form of T1_frozen_instantiated)
   ================================================================================================== *)

Section MLT1Inst.

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
  Variable LS : list (Event * Event).

  Hypothesis Hpo_trans : forall a b c, po a b -> po b c -> po a c.
  Hypothesis rw_disjoint : forall e, is_read e -> is_write e -> False.

  (* each lane: the pair facts, plus the token commitments that derive po-twin and r12 *)
  Record LaneTok (k d : Event) : Prop := {
    t_k_in  : In k E0;
    t_d_in  : In d E0;
    t_k_w   : is_write k;
    t_d_w   : is_write d;
    t_gmo   : gmo k d;
    t_po    : po k d;
    t_hart  : hart d = hart k;
    t_foot  : forall b, touches d b -> touches k b;
    t_val   : forall b, touches d b -> wval k b = wval d b;
    t_adj   : forall b, touches d b ->
                forall w, In w E0 -> is_write w -> touches w b -> ~ (gmo k w /\ gmo w d);
    (* localized po-linearity: events po-before the replay are po-comparable to the first attempt *)
    t_total : forall e, e <> k -> po e d -> po e k \/ po k e;
    (* a read of this lane's bytes is never po-between the lane's first attempt and its replay *)
    t_fp    : forall a x, is_read a -> touches a x -> touches d x -> ~ (po k a /\ po a d);
    (* first attempt and replay are occurrences of one static instruction *)
    t_deps  : forall e, (addr e k -> addr e d) /\ (data e k -> data e d);
    (* a same-hart reader of the replay is po-after it *)
    t_rdr   : forall bb c, po k c -> rf d bb c -> po d c
  }.

  Lemma LaneTok_LaneOK : forall k d, LaneTok k d ->
    LaneOK Event Byte Hart Value gmo is_write is_read touches wval addr data hart E0 rf po k d.
  Proof.
    intros k d T. destruct T.
    constructor; try assumption.
    - intros a c x Ra Tax Tdx Pad Pdc.
      exact (Token_model.po_twin_derived Event Byte po is_read is_write touches
               Hpo_trans d k t_po0 t_k_w0 rw_disjoint t_total0 t_fp0 a c x Ra Tax Tdx Pad Pdc).
    - intros a c bb Hak Hkc Hdep Hrf.
      exact (Token_model.dup_r12_derived Event Byte po Hpo_trans d k t_po0 rf addr data
               t_deps0 t_rdr0 a c bb Hak Hkc Hdep Hrf).
  Qed.

  Hypothesis Hirr : forall e, In e E0 -> ~ gmo e e.
  Hypothesis Htr  : forall a b c, In a E0 -> In b E0 -> In c E0 -> gmo a b -> gmo b c -> gmo a c.
  Hypothesis Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.
  Hypothesis rf_is_C4 : forall b r w, is_read r -> In r E0 -> rf w b r ->
      L1_abstract_erasure.C4_source Event Byte is_write touches gmo po E0 b r w.
  Hypothesis rf_touches : forall w b r, rf w b r -> touches w b.
  Hypothesis rf_functional : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.
  Hypothesis Hlanes : forall k d, In (k, d) LS -> LaneTok k d.
  Hypothesis keeper_survives : forall k d, In (k, d) LS -> ~ ML_base.isdel Event LS k.

  Theorem ML_T1_refinement_instantiated :
    (forall x, ~ clos_trans Event
       (Clift_coherence.Cf Event Byte gmo is_write is_read touches E0 rf poloc) x x) ->
    (forall x, ~ clos_trans Event
       (Frozen_mainmodel.FRf Event Byte Hart gmo is_write is_read is_load is_store touches
          same_addr addr data ctrl fence hart E0 rf po) x x) ->
    exists (E_N : list Event) (rf_N : Event -> Byte -> Event -> Prop),
      E_N = ML_base.carrier_L Event eq_ev_dec E0 LS /\
      rf_N = ML_base.rf_L Event LS Byte rf /\
      (forall x, ~ clos_trans Event
         (Cn_L Event Byte gmo is_write is_read touches E0 rf poloc LS) x x) /\
      (forall x, ~ clos_trans Event
         (Rn_L Event Byte Hart gmo is_write is_read is_load is_store touches same_addr addr data
            ctrl fence hart E0 rf po LS) x x) /\
      L1_abstract_erasure.L1_consistent Event Byte is_write is_read touches gmo po E_N rf_N /\
      (forall r b w, In r E_N -> is_read r -> rf w b r ->
         exists w', rf_N w' b r /\ wval w' b = wval w b) /\
      (forall b w_f,
         Obs_final_state.co_max_of Event Byte gmo is_write touches (Obs_final_state.inE0 Event E0) b w_f ->
         exists w_n, Obs_final_state.co_max_of Event Byte gmo is_write touches
                       (ML_base.survivor_L Event E0 LS) b w_n /\
                     wval w_f b = wval w_n b).
  Proof.
    apply (ML_T1_refinement Event eq_ev_dec Byte Hart Value gmo is_write is_read is_load is_store
             touches wval same_addr addr data ctrl fence hart E0 rf po poloc LS
             Hirr Htr Htot Hpo_trans rf_is_C4 rf_touches rf_functional).
    - intros k d H. apply LaneTok_LaneOK. apply Hlanes. exact H.
    - exact keeper_survives.
  Qed.

End MLT1Inst.
