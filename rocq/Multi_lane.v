(* Multi_lane.v — the duplicate erasure iterates over several provisional lanes.
 *
 * The frozen family fixes one provisional lane, and L1 contracts one duplicate pair. The vector
 * specification permits SEVERAL elements past vstart to have been written, so the general scenario
 * is a finite set of duplicate pairs. This file mechanizes that iteration.
 *
 * Two things have to be proved, and the second is the content:
 *
 *   1. the erasure composes -- erase_all folds contract_carrier over the deleted duplicates and
 *      rf_all folds rf_retarget over the same list, and read values survive the whole fold;
 *
 *   2. the load-value rule survives ONE step, i.e. rf_retarget preserves C4_source. This is where
 *      gamma_adj earns its keep: after the deleted duplicate d goes, a competing write w' that was
 *      coherence-earlier than d must now be coherence-earlier than the keeper k, and that is
 *      exactly the statement that no write lies coherence-between k and d.
 *
 * No Admitted, no axioms. Coq 8.15.
 *)

From Coq Require Import List Arith.
Import ListNotations.

Section MultiLane.

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte  : Type.
  Variable Value : Type.

  Variable is_write : Event -> Prop.
  Variable is_read  : Event -> Prop.
  Variable touches  : Event -> Byte -> Prop.
  Variable wval     : Event -> Byte -> Value.

  Variable gmo : Event -> Event -> Prop.
  Variable po  : Event -> Event -> Prop.

  Hypothesis gmo_trans : forall x y z, gmo x y -> gmo y z -> gmo x z.
  Hypothesis gmo_irrefl : forall x, ~ gmo x x.

  (* Coherence is a total order on the writes to a byte; this is the per-location totality the
     memory model already provides, not a new assumption about the erasure. *)
  Hypothesis gmo_total_w :
    forall x y, is_write x -> is_write y -> x <> y -> gmo x y \/ gmo y x.

  Hypothesis po_trans : forall x y z, po x y -> po y z -> po x z.

  (* ---------------------------------------------------------------- carriers and retargeting *)

  Definition drop (d : Event) (E : list Event) : list Event :=
    filter (fun e => if eq_ev_dec e d then false else true) E.

  Lemma drop_sub : forall d e E, In e (drop d E) -> In e E.
  Proof. intros d e E H. apply filter_In in H. destruct H as [H _]; exact H. Qed.

  Lemma drop_neq : forall d e E, In e (drop d E) -> e <> d.
  Proof.
    intros d e E H. apply filter_In in H. destruct H as [_ H].
    destruct (eq_ev_dec e d) as [Ed|Nd]; [discriminate H | exact Nd].
  Qed.

  Lemma drop_in : forall d e E, In e E -> e <> d -> In e (drop d E).
  Proof.
    intros d e E H Hne. apply filter_In. split; [exact H|].
    destruct (eq_ev_dec e d) as [Ed|Nd]; [contradiction | reflexivity].
  Qed.

  Definition retarget (d k : Event) (r1 : Event -> Byte -> Event -> Prop)
    : Event -> Byte -> Event -> Prop :=
    fun w b rd => (r1 w b rd /\ ~ r1 d b rd) \/ (r1 d b rd /\ w = k).

  (* ------------------------------------------------------------------------ the load-value rule *)

  Definition cand (E : list Event) (b : Byte) (rd w : Event) : Prop :=
    In w E /\ is_write w /\ touches w b /\ (gmo w rd \/ po w rd).

  Definition C4 (E : list Event) (rf : Event -> Byte -> Event -> Prop) : Prop :=
    forall b rd w, is_read rd -> In rd E -> rf w b rd ->
      cand E b rd w /\ forall w', cand E b rd w' -> w' = w \/ gmo w' w.

  (* ----------------------------------------------------------------------- duplicate structure *)

  Record Dup (p q : Event) : Prop := {
    d_wp   : is_write p;
    d_wq   : is_write q;
    d_foot : forall b, touches p b <-> touches q b;
    d_val  : forall b, touches p b -> wval p b = wval q b
  }.

  (* no write lies coherence-strictly between the keeper and the deleted duplicate, at any byte *)
  Definition adj (E : list Event) (k d : Event) : Prop :=
    forall z, In z E -> is_write z -> z <> k -> z <> d -> ~ (gmo k z /\ gmo z d).

  (* ------------------------------------------------- one step preserves the load-value rule ---- *)

  Lemma retarget_preserves_C4 :
    forall E rf k d,
      C4 E rf ->
      In k E -> k <> d ->
      is_write k -> (forall b, touches d b -> touches k b) ->
      gmo k d -> po k d ->
      adj E k d ->
      C4 (drop d E) (retarget d k rf).
  Proof.
    intros E rf k d HC4 Hk_in Hkd Hwk Hfoot Hkd_gmo Hkd_po Hadj.
    intros b rd w Hrd Hrd_in Hret.
    assert (Hrd_E : In rd E) by (eapply drop_sub; exact Hrd_in).
    destruct Hret as [[Hrf Hnd] | [Hrfd Hwk_eq]].
    - (* the source survived: it is still the C4 source over the smaller carrier *)
      destruct (HC4 b rd w Hrd Hrd_E Hrf) as [[Hin [Hw [Ht Hord]]] Hmax].
      split.
      + repeat split; try assumption.
        apply drop_in; [exact Hin|].
        intro Heq; subst w; contradiction.
      + intros w' Hc'. apply Hmax.
        destruct Hc' as [Hin' Hrest]. split; [eapply drop_sub; exact Hin' | exact Hrest].
    - (* the source was deleted: the keeper takes its place *)
      subst w.
      destruct (HC4 b rd d Hrd Hrd_E Hrfd) as [[Hin_d [Hw_d [Ht_d Hord_d]]] Hmax_d].
      assert (Htk : touches k b) by (apply Hfoot; exact Ht_d).
      assert (Hkr : gmo k rd \/ po k rd).
      { destruct Hord_d as [Hgd | Hpd].
        - left. eapply gmo_trans; [exact Hkd_gmo | exact Hgd].
        - (* d is po-before the read, and the keeper is po-before d: the re-execution orientation
             puts the first attempt ahead of the replay, so the keeper is po-before the read too. *)
          right. eapply po_trans; [exact Hkd_po | exact Hpd]. }
      split.
      + repeat split.
        * apply drop_in; [exact Hk_in | exact Hkd].
        * exact Hwk.
        * exact Htk.
        * exact Hkr.
      + intros w' Hc'.
        destruct Hc' as [Hin' [Hw' [Ht' Hord']]].
        assert (Hin'E : In w' E) by (eapply drop_sub; exact Hin').
        assert (Hne'd : w' <> d) by (eapply drop_neq; exact Hin').
        destruct (eq_ev_dec w' k) as [Ek | Nk]; [left; exact Ek | right].
        (* w' competes with d, so it is d or coherence-earlier; it is not d, so it is earlier,
           and gamma_adj forbids it from sitting between k and d. *)
        destruct (Hmax_d w') as [Ed' | Hg'd].
        * repeat split; assumption.
        * contradiction.
        * (* gmo w' d, w' <> k, w' <> d: adjacency rules out gmo k w', so w' is before k *)
          destruct (gmo_total_w w' k Hw' Hwk Nk) as [Hgk | Hkw].
          -- exact Hgk.
          -- exfalso. apply (Hadj w' Hin'E Hw' Nk Hne'd).
             split; [exact Hkw | exact Hg'd].
  Qed.


  (* ------------------------------------------------------- the iteration over provisional lanes *)

  (* A lane is a keeper/deleted pair. The vector specification permits several elements past vstart
     to have been written, so the general scenario is a list of these, one per provisional lane. *)
  Definition lane := (Event * Event)%type.

  Fixpoint erase_all (ls : list lane) (E : list Event) : list Event :=
    match ls with
    | [] => E
    | (_, d) :: t => erase_all t (drop d E)
    end.

  Fixpoint rf_all (ls : list lane) (r : Event -> Byte -> Event -> Prop)
    : Event -> Byte -> Event -> Prop :=
    match ls with
    | [] => r
    | (k, d) :: t => rf_all t (retarget d k r)
    end.

  (* What each lane must satisfy against the carrier it is applied to. Distinct lanes have disjoint
     byte footprints, so these are per-lane conditions rather than joint ones. *)
  Definition lane_ok (E : list Event) (kd : lane) : Prop :=
    let (k, d) := kd in
    In k E /\ k <> d /\ is_write k
    /\ (forall b, touches d b -> touches k b)
    /\ (forall b, touches d b -> wval k b = wval d b)
    /\ gmo k d /\ po k d /\ adj E k d.

  Fixpoint lanes_ok (ls : list lane) (E : list Event) : Prop :=
    match ls with
    | [] => True
    | (k, d) :: t => lane_ok E (k, d) /\ lanes_ok t (drop d E)
    end.

  (* The two footprint conditions of lane_ok are exactly what a duplicate pair provides, so a lane
     built from a DupPair in the keeper orientation satisfies them. Nothing extra is assumed. *)
  Lemma dup_gives_agreement :
    forall p q k d,
      Dup p q -> (d = p /\ k = q) \/ (d = q /\ k = p) ->
      (forall b, touches d b -> touches k b)
      /\ (forall b, touches d b -> wval k b = wval d b).
  Proof.
    intros p q k d Hdup Horient.
    destruct Hdup as [Wp Wq Dfoot Dval].
    destruct Horient as [[Ed Ek] | [Ed Ek]]; subst d; subst k; split; intros b Ht.
    - apply (proj1 (Dfoot b)); exact Ht.
    - symmetry; apply Dval; exact Ht.
    - apply (proj2 (Dfoot b)); exact Ht.
    - apply Dval; apply (proj2 (Dfoot b)); exact Ht.
  Qed.

  (* The load-value rule survives the whole fold: erasing every provisional duplicate at once leaves
     a carrier on which reads still obey C4. *)
  Theorem erase_all_preserves_C4 :
    forall ls E rf, C4 E rf -> lanes_ok ls E -> C4 (erase_all ls E) (rf_all ls rf).
  Proof.
    induction ls as [| [k d] t IH]; intros E rf HC4 Hok.
    - exact HC4.
    - simpl in *.
      destruct Hok as [[Hk_in [Hkd [Hwk [Hfoot [_ [Hgmo [Hpo Hadj]]]]]]] Hrest].
      apply IH; [| exact Hrest].
      apply retarget_preserves_C4; assumption.
  Qed.

  (* One step: a read keeps a source, and the value it sees at the byte is unchanged. *)
  Lemma step_preserves_value :
    forall (rf : Event -> Byte -> Event -> Prop) k d rd b w,
      (forall b', touches d b' -> touches k b') ->
      (forall b', touches d b' -> wval k b' = wval d b') ->
      (forall w1 w2, rf w1 b rd -> rf w2 b rd -> w1 = w2) ->
      rf w b rd -> touches w b ->
      exists w', retarget d k rf w' b rd /\ wval w' b = wval w b /\ touches w' b.
  Proof.
    intros rf k d rd b w Hfoot Hval Huniq Hrf Htw.
    destruct (eq_ev_dec w d) as [Ewd | Nwd].
    - subst w. exists k. split; [| split].
      + right; split; [exact Hrf | reflexivity].
      + apply Hval; exact Htw.
      + apply Hfoot; exact Htw.
    - exists w. split; [| split; [reflexivity | exact Htw]].
      left. split; [exact Hrf |]. intro Hd. apply Nwd. apply (Huniq w d Hrf Hd).
  Qed.

  (* Read values survive the whole fold. This is the multi-lane form of L1's value preservation:
     every provisional lane is contracted, and every retained read still sees its byte value. *)
  Theorem erase_all_preserves_values :
    forall ls E (rf : Event -> Byte -> Event -> Prop),
      lanes_ok ls E ->
      (forall b rd w1 w2, rf w1 b rd -> rf w2 b rd -> w1 = w2) ->
      forall b rd w, rf w b rd -> touches w b ->
        exists w', rf_all ls rf w' b rd /\ wval w' b = wval w b /\ touches w' b.
  Proof.
    induction ls as [| [k d] t IH]; intros E rf Hok Huniq b rd w Hrf Htw.
    - exists w; split; [exact Hrf | split; [reflexivity | exact Htw]].
    - simpl in *.
      destruct Hok as [[Hk_in [Hkd [Hwk [Hfoot [Hval [Hgmo [Hpo Hadj]]]]]]] Hrest].
      assert (Huniq' : forall b' rd' w1 w2,
                 retarget d k rf w1 b' rd' -> retarget d k rf w2 b' rd' -> w1 = w2).
      { intros b' rd' w1 w2 H1 H2.
        destruct H1 as [[Ha Hna] | [Ha Hea]]; destruct H2 as [[Hb Hnb] | [Hb Heb]].
        - apply (Huniq b' rd' w1 w2 Ha Hb).
        - exfalso; apply Hna; exact Hb.
        - exfalso; apply Hnb; exact Ha.
        - subst; reflexivity. }
      destruct (step_preserves_value rf k d rd b w Hfoot Hval (Huniq b rd) Hrf Htw)
        as [w1 [Hr1 [Hv1 Ht1]]].
      destruct (IH (drop d E) (retarget d k rf) Hrest Huniq' b rd w1 Hr1 Ht1)
        as [w2 [Hr2 [Hv2 Ht2]]].
      exists w2. repeat split; [exact Hr2 | rewrite Hv2; exact Hv1 | exact Ht2].
  Qed.

End MultiLane.
