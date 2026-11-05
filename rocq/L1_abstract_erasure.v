(* L1_abstract_erasure.v — RESTART-V M4, Layer 1 (abstract duplicate-erasure kernel).

   Architecture-independent: depends ONLY on an abstract memory-consistency interface plus the
   RestartOrder consequences (RO-E / RO-K) and the gamma_adj adjacency condition. No PMP, mret,
   handler encodings, or RISC-V ISA appear here.

   Mechanizes the core of the D-a v1.2 duplicate-erasure argument (attack/round10_dav12_response.md
   §16; delta-audit DELTA 1/3/4). Two modelling decisions the delta audit made precise are honoured:
     * C4 candidacy is CARRIER-RELATIVE (a deleted duplicate is no longer a competitor);
     * duplicates are WHOLE-FOOTPRINT equal (same touched bytes, equal value on each), matching
       D-a Cand_F (bytes(W_first)=bytes(W_replay)=B_j, equal values).

   Status: L1 abstract kernel FULLY MECHANIZED (0 Admitted). This is one layer of the 4-layer plan
   (L2 packages PPO r1-r13 / C1-C7 / C3-G; L3 the handler L1/L1b; L4 the RestartOrder
   instantiations). Nothing is "proved" in the project sense until every layer is discharged and
   human-verified (guide §9.4). Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Section AbstractModel.

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte  : Type.
  Variable Value : Type.

  Variable is_write : Event -> Prop.
  Variable is_read  : Event -> Prop.
  Variable touches  : Event -> Byte -> Prop.
  Variable wval     : Event -> Byte -> Value.

  Variable E0  : list Event.
  Variable gmo : Event -> Event -> Prop.

  Record gmo_wf : Prop := {
    gmo_irrefl : forall e, In e E0 -> ~ gmo e e;
    gmo_trans  : forall a b c, In a E0 -> In b E0 -> In c E0 ->
                               gmo a b -> gmo b c -> gmo a c;
    gmo_total  : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a
  }.

  Variable rf : Event -> Byte -> Event -> Prop.
  Variable po : Event -> Event -> Prop.

  (* Carrier-relative C4 candidate set + source. *)
  Definition cand (E : list Event) (b : Byte) (r w : Event) : Prop :=
    In w E /\ is_write w /\ touches w b /\ (gmo w r \/ po w r).

  Definition C4_source (E : list Event) (b : Byte) (r w : Event) : Prop :=
    cand E b r w /\ forall w', cand E b r w' -> w' = w \/ gmo w' w.

  (* Interface: rf realizes the C4 load-value rule over the full carrier E0. *)
  Hypothesis rf_is_C4 :
    forall b r w, is_read r -> In r E0 -> rf w b r -> C4_source E0 b r w.

  (* Interface: a byte-b source touches byte b. *)
  Hypothesis rf_touches :
    forall w b r, rf w b r -> touches w b.

  (* Reads and writes are disjoint event classes (round-13 audit: lets the retained read r be proved
     distinct from the duplicate writes p,q, which the external po-envelope needs). *)
  Hypothesis rw_disjoint : forall e, is_read e -> is_write e -> False.

  (* ---- Whole-footprint equal duplicates + gamma_adj (per byte) ---- *)

  Record DupPair (p q : Event) : Prop := {
    dp_wp   : is_write p;
    dp_wq   : is_write q;
    dp_foot : forall b, touches p b <-> touches q b;
    dp_val  : forall b, touches p b -> wval p b = wval q b
  }.

  Definition between (b : Byte) (p q z : Event) : Prop :=
    is_write z /\ touches z b /\ z <> p /\ z <> q /\
    ((gmo p z /\ gmo z q) \/ (gmo q z /\ gmo z p)).

  Definition gamma_adj (b : Byte) (p q : Event) : Prop :=
    ~ exists z, In z E0 /\ between b p q z.

  Definition is_keeper (p q k : Event) : Prop :=
    (k = p /\ gmo p q) \/ (k = q /\ gmo q p).

  (* RestartOrder consequences used by erasure (RO-K keeper + RO-E po-envelope). *)
  Record RO_K (p q k : Event) : Prop := {
    rok_earlier : is_keeper p q k;
    (* Re-execution program-order fact (self-check #2 CG-2 fix). The KEEPER is program-order before the
       deleted duplicate. This REPLACES the earlier external po-envelope
       `forall e, e<>p -> e<>q -> (po p e <-> po q e)`, which was UNSATISFIABLE for a real trap
       execution: any trap-region event h (e.g. the handler's footprint probe) has `po keeper h` but not
       `po deleted h` — since `po keeper deleted` and h is po-between them — so the envelope's
       `po p h <-> po q h` fails, and h is neither p nor q. The envelope was ONLY ever consulted to
       transfer po from the deleted duplicate to the keeper at a retained read r (which reads the deleted
       duplicate, hence is po-after it); `po keeper deleted` + transitivity does exactly that, and it IS
       satisfiable — it is the re-execution orientation `po k d`. *)
    rok_po_kd   : (k = p -> po p q) /\ (k = q -> po q p)
  }.

  (* ---- Contraction carrier ---- *)

  Definition contract_carrier (d : Event) : list Event :=
    filter (fun e => if eq_ev_dec e d then false else true) E0.

  Lemma contract_carrier_sub : forall d e, In e (contract_carrier d) -> In e E0.
  Proof.
    intros d e H. unfold contract_carrier in H. apply filter_In in H.
    destruct H as [H _]; exact H.
  Qed.

  Lemma contract_carrier_not_d : forall d e, In e (contract_carrier d) -> e <> d.
  Proof.
    intros d e H. unfold contract_carrier in H. apply filter_In in H.
    destruct H as [_ H]. destruct (eq_ev_dec e d) as [E|N]; [discriminate H|exact N].
  Qed.

  Lemma In_contract : forall d e, In e E0 -> e <> d -> In e (contract_carrier d).
  Proof.
    intros d e H Hne. unfold contract_carrier. apply filter_In. split; [exact H|].
    destruct (eq_ev_dec e d) as [E|N]; [exfalso; apply Hne; exact E | reflexivity].
  Qed.

  (* ---- Trivial supporting lemmas (PROVED) ---- *)

  Lemma gmo_wf_restrict :
    forall (E1 : list Event),
      (forall e, In e E1 -> In e E0) -> gmo_wf ->
      (forall e, In e E1 -> ~ gmo e e) /\
      (forall a b c, In a E1 -> In b E1 -> In c E1 -> gmo a b -> gmo b c -> gmo a c) /\
      (forall a b, In a E1 -> In b E1 -> a <> b -> gmo a b \/ gmo b a).
  Proof.
    intros E1 Hsub [Hirr Htr Htot]. split; [| split].
    - intros e He. apply Hirr. apply Hsub. exact He.
    - intros a b c Ha Hb Hc Hab Hbc.
      apply (Htr a b c (Hsub a Ha) (Hsub b Hb) (Hsub c Hc) Hab Hbc).
    - intros a b Ha Hb Hne. apply (Htot a b (Hsub a Ha) (Hsub b Hb) Hne).
  Qed.

  (* Uniqueness of the C4 source over any carrier E included in E0. *)
  Lemma C4_source_unique :
    gmo_wf ->
    forall (E : list Event), (forall e, In e E -> In e E0) ->
    forall b r w w',
      C4_source E b r w -> C4_source E b r w' -> w = w'.
  Proof.
    intros Hwf E Hsub b r w w' [Hcw Hmw] [Hcw' Hmw'].
    destruct (eq_ev_dec w w') as [E1|N]; [exact E1|].
    destruct (Hmw w' Hcw') as [Ee|G1].
    - symmetry; exact Ee.
    - destruct (Hmw' w Hcw) as [Ee|G2].
      + exact Ee.
      + exfalso. destruct Hwf as [Hirr Htr _].
        destruct Hcw as [Inw _]. destruct Hcw' as [Inw' _].
        apply (Hirr w (Hsub w Inw)).
        apply (Htr w w' w (Hsub w Inw) (Hsub w' Inw') (Hsub w Inw) G2 G1).
  Qed.

  (* Shrinking the carrier preserves a source that survives (fewer competitors). *)
  Lemma C4_shrink :
    forall (E E' : list Event) b r w,
      (forall e, In e E' -> In e E) -> In w E' ->
      C4_source E b r w -> C4_source E' b r w.
  Proof.
    intros E E' b r w Hsub Hin [Hcand Hmax]. split.
    - destruct Hcand as [_ [Ww [Tw Ord]]].
      split; [exact Hin|]. split; [exact Ww|]. split; [exact Tw|exact Ord].
    - intros w' Hcw'. apply Hmax. destruct Hcw' as [Hin' rest].
      split; [apply Hsub; exact Hin' | exact rest].
  Qed.

  (* ---- Retargeting kernel (PROVED) ---- *)

  (* Order-theoretic core: under gamma_adj at byte b and the RO-E po-envelope, if a read r had the
     DELETED duplicate d as its C4 source over E0, then the retained keeper k is the C4 source of
     byte b of r over the SURVIVING carrier (contract_carrier d). *)
  Lemma retarget_keeper_is_source :
    gmo_wf ->
    (forall a b c, po a b -> po b c -> po a c) ->      (* po transitivity (CG-2 fix: envelope→trans) *)
    forall b p q k d r,
      In p E0 -> In q E0 ->
      DupPair p q ->
      RO_K p q k ->
      (d = p \/ d = q) -> k <> d ->
      gamma_adj b p q ->
      In r E0 -> is_read r ->
      C4_source E0 b r d ->
      C4_source (contract_carrier d) b r k.
  Proof.
    intros Hwf Hpotrans b p q k d r Hp Hq Hdup Hrok Hdpq Hkd Hadj Hr Hrd Hsrc.
    destruct Hwf as [Hirr Htr Htot].
    destruct Hdup as [Wp Wq Dfoot Dval].
    destruct Hrok as [Hkeep Hpokd].
    destruct Hsrc as [Hcandd Hmaxd].
    destruct Hcandd as [Ind [Wd [Td Hordd]]].
    (* the read r is distinct from both writes p,q — needed to consult the external envelope at r *)
    assert (Hrp : r <> p) by (intro E; apply (rw_disjoint r Hrd); rewrite E; exact Wp).
    assert (Hrq : r <> q) by (intro E; apply (rw_disjoint r Hrd); rewrite E; exact Wq).
    (* touches p b and touches q b, from touches d b and d in {p,q}. *)
    assert (Tpq : touches p b /\ touches q b).
    { destruct Hdpq as [Ed|Ed].
      - subst d. split; [exact Td | apply (proj1 (Dfoot b)); exact Td].
      - subst d. split; [apply (proj2 (Dfoot b)); exact Td | exact Td]. }
    destruct Tpq as [Tp Tq].
    destruct Hkeep as [[Ek Gpq]|[Ek Gqp]].
    - (* keeper k = p *) subst k.
      destruct Hdpq as [Ed|Ed]; subst d.
      + exfalso; apply Hkd; reflexivity.
      + split.
        * split; [apply In_contract; [exact Hp | exact Hkd] |].
          split; [exact Wp|]. split; [exact Tp|].
          destruct Hordd as [Gqr|Pqr].
          -- left. apply (Htr p q r Hp Hq Hr Gpq Gqr).
          -- (* CG-2: po p r from po p q (keeper po-before deleted) + po q r, by transitivity *)
             right. apply (Hpotrans p q r (proj1 Hpokd eq_refl) Pqr).
        * intros w' Hcw'.
          destruct Hcw' as [Hw'in [Ww' [Tw' Ord']]].
          assert (Hw'0 : In w' E0) by (apply (contract_carrier_sub q); exact Hw'in).
          assert (Hw'q : w' <> q) by (apply (contract_carrier_not_d q); exact Hw'in).
          destruct (Hmaxd w' (conj Hw'0 (conj Ww' (conj Tw' Ord')))) as [Ewq|Gw'q].
          -- exfalso; apply Hw'q; exact Ewq.
          -- destruct (eq_ev_dec w' p) as [Ewp|Nwp]; [left; exact Ewp|].
             right.
             destruct (Htot w' p Hw'0 Hp Nwp) as [Gw'p|Gpw'].
             ++ exact Gw'p.
             ++ exfalso. apply Hadj. exists w'. split; [exact Hw'0|].
                split; [exact Ww'|]. split; [exact Tw'|].
                split; [exact Nwp|]. split; [exact Hw'q|].
                left. split; [exact Gpw' | exact Gw'q].
    - (* keeper k = q *) subst k.
      destruct Hdpq as [Ed|Ed]; subst d.
      + split.
        * split; [apply In_contract; [exact Hq | exact Hkd] |].
          split; [exact Wq|]. split; [exact Tq|].
          destruct Hordd as [Gpr|Ppr].
          -- left. apply (Htr q p r Hq Hp Hr Gqp Gpr).
          -- (* CG-2: po q r from po q p (keeper po-before deleted) + po p r, by transitivity *)
             right. apply (Hpotrans q p r (proj2 Hpokd eq_refl) Ppr).
        * intros w' Hcw'.
          destruct Hcw' as [Hw'in [Ww' [Tw' Ord']]].
          assert (Hw'0 : In w' E0) by (apply (contract_carrier_sub p); exact Hw'in).
          assert (Hw'p : w' <> p) by (apply (contract_carrier_not_d p); exact Hw'in).
          destruct (Hmaxd w' (conj Hw'0 (conj Ww' (conj Tw' Ord')))) as [Ewp|Gw'p].
          -- exfalso; apply Hw'p; exact Ewp.
          -- destruct (eq_ev_dec w' q) as [Ewq|Nwq]; [left; exact Ewq|].
             right.
             destruct (Htot w' q Hw'0 Hq Nwq) as [Gw'q|Gqw'].
             ++ exact Gw'q.
             ++ exfalso. apply Hadj. exists w'. split; [exact Hw'0|].
                split; [exact Ww'|]. split; [exact Tw'|].
                split; [exact Hw'p|]. split; [exact Nwq|].
                right. split; [exact Gqw' | exact Gw'p].
      + exfalso; apply Hkd; reflexivity.
  Qed.

  (* ---- L1 consistency bundle + contraction + main theorems ---- *)

  Record L1_consistent (E1 : list Event) (rf1 : Event -> Byte -> Event -> Prop) : Prop := {
    l1_gmo : (forall e, In e E1 -> ~ gmo e e) /\
             (forall a b c, In a E1 -> In b E1 -> In c E1 -> gmo a b -> gmo b c -> gmo a c) /\
             (forall a b, In a E1 -> In b E1 -> a <> b -> gmo a b \/ gmo b a);
    l1_c4  : forall b r w, is_read r -> In r E1 -> rf1 w b r -> C4_source E1 b r w
  }.

  Definition rf_retarget (d k : Event) (rf1 : Event -> Byte -> Event -> Prop)
             : Event -> Byte -> Event -> Prop :=
    fun w b r => (rf1 w b r /\ ~ rf1 d b r) \/ (rf1 d b r /\ w = k).

  (* Read-value preservation: every retained read gets a retargeted source of equal byte value. *)
  Theorem L1_erasure_preserves_read_values :
    gmo_wf ->
    forall p q k d r b w,
      DupPair p q -> RO_K p q k ->
      (d = p \/ d = q) -> k <> d ->
      In r (contract_carrier d) -> is_read r ->
      rf w b r ->
      exists w', rf_retarget d k rf w' b r /\ wval w' b = wval w b.
  Proof.
    intros Hwf p q k d r b w Hdup Hrok Hdpq Hkd Hr_in Hrd Hrf.
    assert (Hr0 : In r E0) by (eapply contract_carrier_sub; exact Hr_in).
    destruct (eq_ev_dec w d) as [Ewd|Nwd].
    - (* read from the deleted duplicate: retarget to keeper k *)
      subst w. exists k. split.
      + right. split; [exact Hrf | reflexivity].
      + (* wval k b = wval d b, from whole-footprint equal values at byte b *)
        assert (Tdb : touches d b) by (apply (rf_touches d b r); exact Hrf).
        destruct Hdup as [Wp Wq Dfoot Dval].
        destruct Hrok as [Hkeep _].
        destruct Hkeep as [[Ek _]|[Ek _]]; subst k;
          destruct Hdpq as [Ed|Ed]; subst d.
        * exfalso; apply Hkd; reflexivity.
        * (* k=p, d=q: wval p b = wval q b via Dval at b (touches p b from touches q b) *)
          apply Dval. apply (proj2 (Dfoot b)). exact Tdb.
        * (* k=q, d=p: wval q b = wval p b *)
          symmetry. apply Dval. exact Tdb.
        * exfalso; apply Hkd; reflexivity.
    - (* source is not the deleted duplicate: keep it *)
      exists w. split.
      + left. split; [exact Hrf|].
        intro Hdrf. apply Nwd.
        assert (Hcw : C4_source E0 b r w) by (apply (rf_is_C4 b r w Hrd Hr0 Hrf)).
        assert (Hcd : C4_source E0 b r d) by (apply (rf_is_C4 b r d Hrd Hr0 Hdrf)).
        apply (C4_source_unique Hwf E0 (fun e H => H) b r w d Hcw Hcd).
      + reflexivity.
  Qed.

  (* Main L1 theorem: contracting one whole-footprint duplicate pair, adjacent at every byte,
     yields an L1-consistent contracted graph (gmo well-formedness on the restricted carrier + the
     carrier-relative C4 load-value rule for the retargeted rf).
     Input consistency is exactly the section interface — `gmo_wf` and the `rf_is_C4` hypothesis
     (which IS `L1_consistent E0 rf`'s `l1_c4` field, asserted globally here); we do NOT take a
     separate `L1_consistent E0 rf` premise, since it would be redundant with that interface and the
     proof would ignore it. So this is honestly "the section's input consistency is preserved by
     contraction", not a record-to-record map consuming an unused argument. *)
  Theorem L1_erasure_preserves_consistency :
    gmo_wf ->
    (forall a b c, po a b -> po b c -> po a c) ->      (* po transitivity (CG-2 fix) *)
    forall p q k d,
      In p E0 -> In q E0 ->
      DupPair p q -> RO_K p q k ->
      (forall b, gamma_adj b p q) ->
      (d = p \/ d = q) -> k <> d ->
      L1_consistent (contract_carrier d) (rf_retarget d k rf).
  Proof.
    intros Hwf Hpotrans p q k d Hp Hq Hdup Hrok Hadj Hdpq Hkd.
    split.
    - (* l1_gmo on the restricted carrier *)
      apply (gmo_wf_restrict (contract_carrier d) (contract_carrier_sub d) Hwf).
    - (* l1_c4 *)
      intros b r w Hrd Hr_in Hretf.
      assert (Hr0 : In r E0) by (apply (contract_carrier_sub d); exact Hr_in).
      destruct Hretf as [[Hrf Hndrf]|[Hdrf Hwk]].
      + (* kept source w; w <> d *)
        assert (Hcw0 : C4_source E0 b r w) by (apply (rf_is_C4 b r w Hrd Hr0 Hrf)).
        assert (Hwd : w <> d).
        { intro Ewd. apply Hndrf. rewrite <- Ewd. exact Hrf. }
        assert (Inw0 : In w E0) by (destruct Hcw0 as [[Inw _] _]; exact Inw).
        apply (C4_shrink E0 (contract_carrier d) b r w
                 (contract_carrier_sub d) (In_contract d w Inw0 Hwd) Hcw0).
      + (* retargeted source w = k *)
        subst w.
        assert (Hcd0 : C4_source E0 b r d) by (apply (rf_is_C4 b r d Hrd Hr0 Hdrf)).
        apply (retarget_keeper_is_source Hwf Hpotrans b p q k d r Hp Hq Hdup Hrok Hdpq Hkd
                 (Hadj b) Hr0 Hrd Hcd0).
  Qed.

End AbstractModel.

(* All lemmas Qed-proved; 0 Admitted. L1 abstract duplicate-erasure kernel complete. *)
