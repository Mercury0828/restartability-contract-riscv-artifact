(* Rlift_mainmodel.v — RESTART-V M4: the MAIN-model witness lift (co ∪ rfe ∪ fr ∪ ppo).

   The companion to Clift_coherence: it lifts the no-fault WITNESS main-model relation Rn into the
   fault-run Rf (each witness edge to a clos_trans Rf path), so — by `acyclic_via_simulation` — Rn is
   acyclic whenever Rf is. This is the Rlift side of Top_T1_skeleton's `witness_acyclic_if_edges_lift`
   (the per-location side is Clift's Cn).

   Edge kinds and how each lifts:
     - co / fr: exactly as in Clift_coherence (co by survivor-inclusion; fr via the adjacency crux).
     - rfe (EXTERNAL rf): if the source is unchanged, same fault rfe edge; if RETARGETED (witness
       k ->rfe r), it lifts to the two-edge fault path  k ->co d ->rfe r. Externality is preserved
       because the two duplicates are on the same hart (hart d = hart k), so hart d <> hart r follows
       from hart k <> hart r.
     - ppo: the ppo-edge lift is NOT proved here — it is taken as the single explicit hypothesis
       `ppo_lifts`. This is the honest reduction: main-model WITNESS acyclicity is reduced to the
       ppo-edge lift, exactly as main-model acyclicity (L2_consistency.Main_model_acyclic) is reduced
       to ppo ⊆ gmo. Discharging `ppo_lifts` needs the concrete PPO r1-r13 semantics and how erasure
       (event removal + rf retargeting) acts on preserved program order — the remaining L2 work.

   Self-contained modulo L2_ppo; 0 Admitted / 0 axioms (Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import RestartV.L2_ppo.
Import ListNotations.

Section Rlift.

  Variable Event : Type.
  Variable Byte : Type.
  Variable Hart : Type.
  Variable gmo : Event -> Event -> Prop.
  Variable is_write is_read : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable hart : Event -> Hart.
  Variable E0 : list Event.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable ppo ppo_wit : Event -> Event -> Prop.   (* fault / witness preserved program order *)
  Variables d k : Event.
  Hypothesis d_in : In d E0.
  Hypothesis d_w  : is_write d.
  Hypothesis k_in : In k E0.
  Hypothesis k_w  : is_write k.
  Hypothesis rf_touches : forall w bb r, rf w bb r -> touches w bb.
  Hypothesis keeper_before : gmo k d.         (* keeper coherence-before deleted duplicate *)
  Hypothesis hart_dk : hart d = hart k.        (* both duplicates on the same hart *)

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

  Definition rfe_flt (x y : Event) : Prop := exists b, rf x b y /\ hart x <> hart y.
  (* rfe_wit carrier-restricted to survivors (round-15 audit: exact witness identification) *)
  Definition rfe_wit (x y : Event) : Prop :=
    exists b, survivor x /\ survivor y /\ rfw x b y /\ hart x <> hart y.

  Definition Rf (x y : Event) : Prop :=
    (exists b, co_flt b x y) \/
    (exists b, is_read x /\ fr_flt b x y) \/
    rfe_flt x y \/
    ppo x y.
  (* Rn carrier-restricted to survivors on every disjunct (round-15 audit): exactly the main-model
     relation of the contracted witness (co_wit carries survivors; fr/rfe now add them; ppo_wit's
     frozen rules carry them). *)
  Definition Rn (x y : Event) : Prop :=
    (exists b, co_wit b x y) \/
    (exists b, survivor x /\ survivor y /\ is_read x /\ fr_wit b x y) \/
    rfe_wit x y \/
    ppo_wit x y.

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
    forall b w2, adj b -> survivor w2 -> is_write w2 -> touches w2 b -> gmo k w2 -> co_flt b d w2.
  Proof.
    intros Hwf b w2 Hadj Hsv Ww2 Tw2 Gkw2.
    destruct Hwf as [Gtot]. destruct Hadj as [Adt [Akt Hbet]]. destruct Hsv as [Inw2 Nw2d].
    assert (Gdw2 : gmo d w2).
    { destruct (Gtot d w2 d_in Inw2 (fun E => Nw2d (eq_sym E))) as [X|X].
      - exact X.
      - exfalso. apply (Hbet w2 Inw2 Ww2 Tw2). split; [exact Gkw2 | exact X]. }
    unfold co_flt, coOn, inE0. repeat split; assumption.
  Qed.

  Lemma keeper_co_d : forall b, adj b -> co_flt b k d.
  Proof.
    intros b Hadj. destruct Hadj as [Tdb [Tkb _]].
    unfold co_flt, coOn, inE0.
    split; [exact k_in|]. split; [exact d_in|]. split; [exact k_w|].
    split; [exact d_w|]. split; [exact Tkb|]. split; [exact Tdb|]. exact keeper_before.
  Qed.

  Lemma Rn_lifts :
    gmo_wf -> (forall b, touches d b -> adj b) ->
    (forall x y, ppo_wit x y -> clos_trans Event Rf x y) ->
    forall x y, Rn x y -> clos_trans Event Rf x y.
  Proof.
    intros Hwf Hadj Hppo x y H.
    destruct H as [[b Hco] | [ [b [_ [_ [Hrx Hfr]]]] | [ Hrfe | Hpp ] ]].
    - (* co *)
      apply t_step. left. exists b. apply co_wit_to_flt; exact Hco.
    - (* fr *)
      apply t_step. right. left. exists b. split; [exact Hrx|].
      unfold fr_wit in Hfr. destruct Hfr as [w1 [Hrfw Hcow]].
      unfold rfw in Hrfw. destruct Hrfw as [[Hrf1 _] | [Hrfd Hw1k]].
      + exists w1. split; [exact Hrf1 | apply co_wit_to_flt; exact Hcow].
      + subst w1.
        assert (Tdb : touches d b) by (apply (rf_touches d b x); exact Hrfd).
        destruct Hcow as [_ [Svy [_ [Wy [_ [Ty Gky]]]]]].
        exists d. split; [exact Hrfd | apply (fr_crux Hwf b y (Hadj b Tdb) Svy Wy Ty Gky)].
    - (* rfe *)
      unfold rfe_wit in Hrfe. destruct Hrfe as [b [_ [_ [Hrfw Hext]]]].
      unfold rfw in Hrfw. destruct Hrfw as [[Hrf1 _] | [Hrfd Hxk]].
      + (* unchanged source *)
        apply t_step. right. right. left. exists b. split; [exact Hrf1 | exact Hext].
      + (* retargeted k -> r: two-edge path  k ->co d ->rfe y, externality preserved *)
        subst x.
        assert (Tdb : touches d b) by (apply (rf_touches d b y); exact Hrfd).
        assert (Hdy : hart d <> hart y) by (rewrite hart_dk; exact Hext).
        apply (t_trans Event Rf k d y).
        * apply t_step. left. exists b. apply (keeper_co_d b (Hadj b Tdb)).
        * apply t_step. right. right. left. exists b. split; [exact Hrfd | exact Hdy].
    - (* ppo: the one assumed lift *)
      apply Hppo; exact Hpp.
  Qed.

  Theorem witness_mainmodel_acyclic :
    gmo_wf -> (forall b, touches d b -> adj b) ->
    (forall x y, ppo_wit x y -> clos_trans Event Rf x y) ->
    (forall x, ~ clos_trans Event Rf x x) ->
    forall x, ~ clos_trans Event Rn x x.
  Proof.
    intros Hwf Hadj Hppo Hacyc.
    apply (acyclic_via_simulation Event Rf Rn).
    - intros x y H. apply (Rn_lifts Hwf Hadj Hppo x y H).
    - exact Hacyc.
  Qed.

End Rlift.
