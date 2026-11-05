(* Clift_coherence.v — RESTART-V M4: the FULL per-location Clift assembled to the path level.

   The per-location coherence check is acyclic(co ∪ rf ∪ fr ∪ po-loc). This file proves that the
   no-fault WITNESS per-location relation Cn lifts, edge by edge, into the fault-run relation Cf
   (each witness edge to a clos_trans Cf PATH), hence — by `acyclic_via_simulation` — Cn is acyclic
   whenever Cf is. Round-12 audit extended this from the co∪fr fragment to all four edge kinds:

     - co edge (two surviving writes): survivor ⊆ E0 and gmo unchanged ⇒ same fault co edge
       (length-1 path). (`co_wit_to_flt`.)
     - fr edge (read r, source w1, w1 <co w2): if the source is unchanged, same fault fr edge; if the
       source was retargeted d→k, the fault fr edge uses source d, supported by gmo k w2 ⇒ gmo d w2
       (adjacency crux `fr_crux`). Length-1 path.
     - rf edge (write w →rf read r): if unchanged, same fault rf edge; if RETARGETED (witness k →rf r
       because r originally read d), it lifts to the genuine TWO-edge fault path  k →co d →rf r,
       using the keeper-before-deleted coherence order gmo k d. (This is the multi-edge case the
       round-12 audit named.)
     - po-loc edge among survivors: po is over the original events; restricting to survivors gives a
       fault po-loc edge (length-1 path, inclusion).

   So this is the complete per-location Clift at the abstract level. What remains for the whole T1:
   the analogous MAIN-model lift (co∪rfe∪fr∪ppo, incl. ppo edges under erasure), and threading the
   concrete witness-execution construction that supplies these relations. Self-contained modulo
   L2_ppo; 0 Admitted / 0 axioms (Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import RestartV.L2_ppo.
Import ListNotations.

Section Clift.

  Variable Event : Type.
  Variable Byte : Type.
  Variable gmo : Event -> Event -> Prop.
  Variable is_write is_read : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable E0 : list Event.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable poloc : Event -> Event -> Prop.
  Variables d k : Event.
  Hypothesis d_in : In d E0.
  Hypothesis d_w  : is_write d.
  Hypothesis k_in : In k E0.
  Hypothesis k_w  : is_write k.
  Hypothesis rf_touches : forall w bb r, rf w bb r -> touches w bb.
  (* keeper is coherence-before the deleted duplicate (L1's is_keeper picks the gmo-earlier one). *)
  Hypothesis keeper_before : gmo k d.

  Record gmo_wf : Prop := {
    g_tot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a
  }.

  Definition survivor (x : Event) : Prop := In x E0 /\ x <> d.
  Definition inE0 (x : Event) : Prop := In x E0.

  Definition coOn (C : Event -> Prop) (b : Byte) (w1 w2 : Event) : Prop :=
    C w1 /\ C w2 /\ is_write w1 /\ is_write w2 /\ touches w1 b /\ touches w2 b /\ gmo w1 w2.
  Definition co_flt := coOn inE0.
  Definition co_wit := coOn survivor.

  Definition rfw (w : Event) (b : Byte) (r : Event) : Prop :=
    (rf w b r /\ ~ rf d b r) \/ (rf d b r /\ w = k).

  Definition fr_flt (b : Byte) (r w2 : Event) : Prop := exists w1, rf w1 b r /\ co_flt b w1 w2.
  Definition fr_wit (b : Byte) (r w2 : Event) : Prop := exists w1, rfw w1 b r /\ co_wit b w1 w2.

  Definition poloc_wit (x y : Event) : Prop := poloc x y /\ survivor x /\ survivor y.

  Definition Cf (x y : Event) : Prop :=
    (exists b, co_flt b x y) \/
    (exists b, is_read x /\ fr_flt b x y) \/
    (exists b, rf x b y) \/
    poloc x y.
  (* Cn is carrier-restricted to survivors on EVERY disjunct, so it is exactly the per-location
     relation of the contracted witness execution (round-15 audit: the rf/fr disjuncts previously
     lacked survivor endpoints, making Cn a conservative super-relation). co_wit/poloc_wit already
     carry survivors; the fr and rf disjuncts now add them explicitly. *)
  Definition Cn (x y : Event) : Prop :=
    (exists b, co_wit b x y) \/
    (exists b, survivor x /\ survivor y /\ is_read x /\ fr_wit b x y) \/
    (exists b, survivor x /\ survivor y /\ rfw x b y) \/
    poloc_wit x y.

  Definition adj (b : Byte) : Prop :=
    touches d b /\ touches k b /\
    forall w, In w E0 -> is_write w -> touches w b -> ~ (gmo k w /\ gmo w d).

  Lemma co_wit_to_flt : forall b w1 w2, co_wit b w1 w2 -> co_flt b w1 w2.
  Proof.
    intros b w1 w2 H. destruct H as [Sv1 [Sv2 [W1 [W2 [T1 [T2 G]]]]]].
    destruct Sv1 as [In1 _]. destruct Sv2 as [In2 _].
    unfold co_flt, coOn, inE0. repeat split; assumption.
  Qed.

  Lemma fr_crux :
    gmo_wf ->
    forall b w2,
      adj b -> survivor w2 -> is_write w2 -> touches w2 b -> gmo k w2 ->
      co_flt b d w2.
  Proof.
    intros Hwf b w2 Hadj Hsv Ww2 Tw2 Gkw2.
    destruct Hwf as [Gtot]. destruct Hadj as [Adt [Akt Hbet]]. destruct Hsv as [Inw2 Nw2d].
    assert (Gdw2 : gmo d w2).
    { destruct (Gtot d w2 d_in Inw2 (fun E => Nw2d (eq_sym E))) as [X|X].
      - exact X.
      - exfalso. apply (Hbet w2 Inw2 Ww2 Tw2). split; [exact Gkw2 | exact X]. }
    unfold co_flt, coOn, inE0. repeat split; assumption.
  Qed.

  (* keeper-before-deleted coherence edge at any byte d touches (adjacency gives touches k b). *)
  Lemma keeper_co_d : forall b, adj b -> co_flt b k d.
  Proof.
    intros b Hadj. destruct Hadj as [Tdb [Tkb _]].
    unfold co_flt, coOn, inE0.
    split; [exact k_in|]. split; [exact d_in|]. split; [exact k_w|].
    split; [exact d_w|]. split; [exact Tkb|]. split; [exact Tdb|]. exact keeper_before.
  Qed.

  (* Every witness per-location edge lifts to a fault-run PATH (clos_trans Cf). *)
  Lemma Cn_lifts :
    gmo_wf -> (forall b, touches d b -> adj b) ->
    forall x y, Cn x y -> clos_trans Event Cf x y.
  Proof.
    intros Hwf Hadj x y H.
    destruct H as [[b Hco] | [ [b [_ [_ [Hrx Hfr]]]] | [ [b [_ [_ Hrfw]]] | Hpl ] ]].
    - (* co edge: length-1 *)
      apply t_step. left. exists b. apply co_wit_to_flt; exact Hco.
    - (* fr edge: length-1 *)
      apply t_step. right. left. exists b. split; [exact Hrx|].
      unfold fr_wit in Hfr. destruct Hfr as [w1 [Hrfw Hcow]].
      unfold rfw in Hrfw. destruct Hrfw as [[Hrf1 _] | [Hrfd Hw1k]].
      + exists w1. split; [exact Hrf1 | apply co_wit_to_flt; exact Hcow].
      + subst w1.
        assert (Tdb : touches d b) by (apply (rf_touches d b x); exact Hrfd).
        destruct Hcow as [_ [Svy [_ [Wy [_ [Ty Gky]]]]]].
        exists d. split; [exact Hrfd | apply (fr_crux Hwf b y (Hadj b Tdb) Svy Wy Ty Gky)].
    - (* rf edge *)
      unfold rfw in Hrfw. destruct Hrfw as [[Hrf1 _] | [Hrfd Hxk]].
      + (* unchanged source: length-1 *)
        apply t_step. right. right. left. exists b. exact Hrf1.
      + (* retargeted k -> r: genuine TWO-edge path  k ->co d ->rf y *)
        subst x.
        assert (Tdb : touches d b) by (apply (rf_touches d b y); exact Hrfd).
        apply (t_trans Event Cf k d y).
        * apply t_step. left. exists b. apply (keeper_co_d b (Hadj b Tdb)).
        * apply t_step. right. right. left. exists b. exact Hrfd.
    - (* po-loc among survivors: length-1 inclusion *)
      apply t_step. right. right. right.
      destruct Hpl as [Hp _]. exact Hp.
  Qed.

  (* The full per-location Clift + acyclicity transfer. *)
  Theorem witness_perloc_acyclic :
    gmo_wf -> (forall b, touches d b -> adj b) ->
    (forall x, ~ clos_trans Event Cf x x) ->
    forall x, ~ clos_trans Event Cn x x.
  Proof.
    intros Hwf Hadj Hacyc.
    apply (acyclic_via_simulation Event Cf Cn).
    - intros x y H. apply (Cn_lifts Hwf Hadj x y H).
    - exact Hacyc.
  Qed.

End Clift.
