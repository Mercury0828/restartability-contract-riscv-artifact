(* Perbyte.v — RESTART-V: the per-location check, read one byte at a time.

   RVWMO is byte-wise. Its per-location check is, for EVERY byte b separately,
       acyclic(co_b ∪ rf_b ∪ fr_b ∪ po-loc_b),
   where po-loc_b is program order on pairs of events that both touch b. `Clift_coherence.Cf` takes the
   union of these edges over all bytes and checks one event graph. The union check is STRONGER: the
   mixed-size run of `Perbyte_example.v` satisfies the load-value rule over a global memory order and
   passes every per-byte check, yet its union graph has a cycle.

   This file
     (1) defines the per-byte check as `Clift_coherence.Cf` at the byte-b restriction of `touches`,
         `rf` and `po-loc` (`touches_at`, `rf_at`, `poloc_at`);
     (2) shows that the union check implies every per-byte check (`union_to_perbyte`), so every run
         covered by the union-graph theorems is covered by the per-byte ones;
     (3) proves that the per-byte check FOLLOWS from RVWMO's own axioms: a strict total global memory
         order, the load-value rule over it, and rules r1 and r2 of preserved program order contained
         in it (`rvwmo_perbyte_coherence`);
     (4) restates Theorem 1 with the per-byte antecedent and the per-byte conclusion
         (`ML_T1_refinement_pb`), reusing ML_T1 by instantiation at each byte;
     (5) restates the Stage-2 capstone the same way (`ML_stage2_endtoend_pb`).

   0 Admitted / 0 axioms (Print Assumptions). Modifies no existing .v file. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import RestartV.L2_ppo.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Obs_final_state.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Rlift_mainmodel.
Require Import RestartV.Frozen_mainmodel.
Require Import RestartV.Ctx_erasure.
Require Import RestartV.Stage2_normal_candidate.
Require Import RestartV.Stage2_obligations.
Require Import RestartV.Frozen_pmp.
Require Import RestartV.Stage2_endtoend_v2.
Require Import RestartV.ML_base.
Require Import RestartV.ML_T1.
Require Import RestartV.ML_stage2.
Import ListNotations.

(* ==================================================================================================
   (1) the byte-b restriction
   ================================================================================================== *)

Section Restrict.
  Variable Event Byte : Type.
  Variable touches : Event -> Byte -> Prop.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable poloc : Event -> Event -> Prop.
  Variable b : Byte.

  Definition touches_at (e : Event) (b' : Byte) : Prop := b' = b /\ touches e b'.
  Definition rf_at (w : Event) (b' : Byte) (r : Event) : Prop := b' = b /\ rf w b' r.
  Definition poloc_at (x y : Event) : Prop := poloc x y /\ touches x b /\ touches y b.
End Restrict.

(* the per-byte check at byte b, and the union check *)
Definition CfB (Event Byte : Type) (gmo : Event -> Event -> Prop) (is_write is_read : Event -> Prop)
    (touches : Event -> Byte -> Prop) (E : list Event) (rf : Event -> Byte -> Event -> Prop)
    (poloc : Event -> Event -> Prop) (b : Byte) : Event -> Event -> Prop :=
  Clift_coherence.Cf Event Byte gmo is_write is_read (touches_at Event Byte touches b) E
    (rf_at Event Byte rf b) (poloc_at Event Byte touches poloc b).

(* ==================================================================================================
   (2) the union check implies every per-byte check
   ================================================================================================== *)

Lemma CfB_sub_Cf : forall Event Byte gmo is_write is_read touches E rf poloc b x y,
    CfB Event Byte gmo is_write is_read touches E rf poloc b x y ->
    Clift_coherence.Cf Event Byte gmo is_write is_read touches E rf poloc x y.
Proof.
  intros Event Byte gmo is_write is_read touches E rf poloc b x y H.
  unfold CfB, Clift_coherence.Cf in *.
  destruct H as [[b' Hco] | [[b' [Rx [w1 [[_ Hrf] Hco]]]] | [[b' [_ Hrf]] | [Hpl _]]]].
  - left. exists b'.
    destruct Hco as [I1 [I2 [W1 [W2 [[_ T1] [[_ T2] G]]]]]].
    unfold Clift_coherence.co_flt, Clift_coherence.coOn. repeat split; assumption.
  - right. left. exists b'. split; [exact Rx |]. exists w1. split; [exact Hrf |].
    destruct Hco as [I1 [I2 [W1 [W2 [[_ T1] [[_ T2] G]]]]]].
    unfold Clift_coherence.co_flt, Clift_coherence.coOn. repeat split; assumption.
  - right. right. left. exists b'. exact Hrf.
  - right. right. right. exact Hpl.
Qed.

Theorem union_to_perbyte : forall Event Byte gmo is_write is_read touches E rf poloc,
    (forall x, ~ clos_trans Event
       (Clift_coherence.Cf Event Byte gmo is_write is_read touches E rf poloc) x x) ->
    forall b x, ~ clos_trans Event (CfB Event Byte gmo is_write is_read touches E rf poloc b) x x.
Proof.
  intros Event Byte gmo is_write is_read touches E rf poloc H b.
  apply (acyclic_sub Event (Clift_coherence.Cf Event Byte gmo is_write is_read touches E rf poloc)).
  - intros x y Hxy. exact (CfB_sub_Cf _ _ _ _ _ _ _ _ _ b x y Hxy).
  - exact H.
Qed.

(* ==================================================================================================
   (3) RVWMO's axioms imply every per-byte check
   ================================================================================================== *)

Section RVWMOPerByte.

  Variable Event Byte : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable gmo : Event -> Event -> Prop.
  Variable is_write is_read : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable E : list Event.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable po poloc : Event -> Event -> Prop.

  (* the global memory order is a strict total order on the events *)
  Hypothesis Hirr : forall e, In e E -> ~ gmo e e.
  Hypothesis Htr  : forall a b c, In a E -> In b E -> In c E -> gmo a b -> gmo b c -> gmo a c.
  Hypothesis Htot : forall a b, In a E -> In b E -> a <> b -> gmo a b \/ gmo b a.
  (* program order is a strict order *)
  Hypothesis Hpo_irr : forall e, ~ po e e.
  Hypothesis Hpo_tr  : forall a b c, po a b -> po b c -> po a c.
  (* typing: an event that touches a byte is a read or a write, not both *)
  Hypothesis Hrw  : forall e, is_read e -> is_write e -> False.
  Hypothesis Hmem : forall e b, In e E -> touches e b -> is_read e \/ is_write e.
  Hypothesis Hpoloc : forall x y, poloc x y -> po x y /\ In x E /\ In y E.
  (* reads-from: the load-value rule; every byte a read touches has exactly one source *)
  Hypothesis Hrf_C4 : forall b r w, is_read r -> In r E -> rf w b r ->
      L1_abstract_erasure.C4_source Event Byte is_write touches gmo po E b r w.
  Hypothesis Hrf_tgt : forall w b r, rf w b r -> is_read r /\ In r E.
  Hypothesis Hrf_fun : forall w1 w2 b r, rf w1 b r -> rf w2 b r -> w1 = w2.
  Hypothesis Hrf_total : forall r b, In r E -> is_read r -> touches r b -> exists w, rf w b r.
  (* ppo rule r1: a store is ordered after an earlier access to an overlapping address *)
  Hypothesis Hr1 : forall x y b, In x E -> In y E -> po x y -> touches x b -> touches y b ->
      is_write y -> gmo x y.
  (* ppo rule r2: two loads of byte b with no store to b between them and different sources *)
  Hypothesis Hr2 : forall x y b, In x E -> In y E -> is_read x -> is_read y ->
      touches x b -> touches y b -> po x y ->
      ~ (exists w, In w E /\ is_write w /\ touches w b /\ po x w /\ po w y) ->
      ~ (exists w, rf w b x /\ rf w b y) -> gmo x y.

  Variable b : Byte.

  Definition PB : Event -> Event -> Prop := CfB Event Byte gmo is_write is_read touches E rf poloc b.

  (* the write whose value an event carries at b: itself for a write, its source for a read *)
  Definition Src (e w : Event) : Prop :=
    In w E /\ ((is_write e /\ w = e) \/ (is_read e /\ rf w b e)).

  Lemma Src_write : forall e w, is_write e -> Src e w -> w = e.
  Proof.
    intros e w We [_ [[_ H] | [Re _]]]; [exact H | exfalso; exact (Hrw e Re We)].
  Qed.

  Lemma Src_read : forall e w, is_read e -> Src e w -> rf w b e.
  Proof.
    intros e w Re [_ [[We _] | [_ H]]]; [exfalso; exact (Hrw e Re We) | exact H].
  Qed.

  Lemma Src_in : forall e w, Src e w -> In w E.
  Proof. intros e w [H _]; exact H. Qed.

  Lemma cand_of_C4 : forall r w, is_read r -> In r E -> rf w b r ->
      In w E /\ is_write w /\ touches w b /\ (gmo w r \/ po w r).
  Proof.
    intros r w Rr Ir Hrf. destruct (Hrf_C4 b r w Rr Ir Hrf) as [[Iw [Ww [Tw O]]] _].
    repeat split; assumption.
  Qed.

  Lemma max_of_C4 : forall r w w', is_read r -> In r E -> rf w b r ->
      In w' E -> is_write w' -> touches w' b -> (gmo w' r \/ po w' r) -> w' = w \/ gmo w' w.
  Proof.
    intros r w w' Rr Ir Hrf Iw' Ww' Tw' O.
    destruct (Hrf_C4 b r w Rr Ir Hrf) as [_ Hmax]. apply Hmax.
    unfold L1_abstract_erasure.cand. repeat split; assumption.
  Qed.

  Definition Inv (x y : Event) : Prop :=
    forall wx wy, Src x wx -> Src y wy ->
      gmo wx wy \/ (wx = wy /\ is_read y /\ (is_write x \/ po x y)).

  (* a read before a write to b in program order: its source is gmo-before the write *)
  Lemma read_then_write : forall x y s, In x E -> In y E -> is_read x -> is_write y ->
      touches x b -> touches y b -> po x y -> rf s b x -> gmo s y.
  Proof.
    intros x y s Ix Iy Rx Wy Tx Ty Pxy Hs.
    destruct (cand_of_C4 x s Rx Ix Hs) as [Is [Ws [Ts [G | P]]]].
    - exact (Htr s x y Is Ix Iy G (Hr1 x y b Ix Iy Pxy Tx Ty Wy)).
    - exact (Hr1 s y b Is Iy (Hpo_tr s x y P Pxy) Ts Ty Wy).
  Qed.

  Lemma edge_src : forall x y, PB x y -> (exists wx, Src x wx) /\ (exists wy, Src y wy).
  Proof.
    intros x y H. unfold PB, CfB, Clift_coherence.Cf in H.
    destruct H as [[b' Hco] | [[b' [Rx [w1 [[Eb Hrf] Hco]]]] | [[b' [Eb Hrf]] | [Hpl [Tx Ty]]]]].
    - destruct Hco as [I1 [I2 [W1 [W2 _]]]].
      split; [exists x | exists y]; split; auto.
    - subst b'. destruct Hco as [I1 [I2 [W1 [W2 _]]]].
      split; [exists w1 | exists y]; split; auto.
    - subst b'. destruct (Hrf_tgt x b y Hrf) as [Ry Iy].
      destruct (cand_of_C4 y x Ry Iy Hrf) as [Ix [Wx _]].
      split; [exists x | exists x]; split; auto.
    - destruct (Hpoloc x y Hpl) as [_ [Ix Iy]].
      split.
      + destruct (Hmem x b Ix Tx) as [Rx | Wx].
        * destruct (Hrf_total x b Ix Rx Tx) as [s Hs].
          exists s. split; [exact (proj1 (cand_of_C4 x s Rx Ix Hs)) | right; auto].
        * exists x. split; auto.
      + destruct (Hmem y b Iy Ty) as [Ry | Wy].
        * destruct (Hrf_total y b Iy Ry Ty) as [s Hs].
          exists s. split; [exact (proj1 (cand_of_C4 y s Ry Iy Hs)) | right; auto].
        * exists y. split; auto.
  Qed.

  Lemma edge_inv : forall x y, PB x y -> Inv x y.
  Proof.
    intros x y H wx wy Sx Sy. unfold PB, CfB, Clift_coherence.Cf in H.
    destruct H as [[b' Hco] | [[b' [Rx [w1 [[Eb Hrf] Hco]]]] | [[b' [Eb Hrf]] | [Hpl [Tx Ty]]]]].
    - (* co *)
      destruct Hco as [I1 [I2 [W1 [W2 [_ [_ G]]]]]].
      rewrite (Src_write x wx W1 Sx), (Src_write y wy W2 Sy). left; exact G.
    - (* fr *)
      subst b'. destruct Hco as [I1 [I2 [W1 [W2 [_ [_ G]]]]]].
      rewrite (Hrf_fun wx w1 b x (Src_read x wx Rx Sx) Hrf), (Src_write y wy W2 Sy).
      left; exact G.
    - (* rf *)
      subst b'. destruct (Hrf_tgt x b y Hrf) as [Ry Iy].
      destruct (cand_of_C4 y x Ry Iy Hrf) as [Ix [Wx _]].
      rewrite (Src_write x wx Wx Sx), (Hrf_fun wy x b y (Src_read y wy Ry Sy) Hrf).
      right. split; [reflexivity |]. split; [exact Ry | left; exact Wx].
    - (* po-loc at b *)
      destruct (Hpoloc x y Hpl) as [Pxy [Ix Iy]].
      destruct (Hmem x b Ix Tx) as [Rx | Wx]; destruct (Hmem y b Iy Ty) as [Ry | Wy].
      + (* read, read *)
        pose proof (Src_read x wx Rx Sx) as Hs1. pose proof (Src_read y wy Ry Sy) as Hs2.
        destruct (cand_of_C4 x wx Rx Ix Hs1) as [I1 [W1 [T1 O1]]].
        destruct (cand_of_C4 y wy Ry Iy Hs2) as [I2 [W2 [T2 O2]]].
        destruct (eq_ev_dec wx wy) as [Heq | Hne].
        * right. split; [exact Heq |]. split; [exact Ry | right; exact Pxy].
        * destruct (Htot wx wy I1 I2 Hne) as [G | G]; [left; exact G |].
          exfalso.
          assert (Hc : gmo wx y \/ po wx y).
          { destruct O1 as [G1 | P1]; [| right; exact (Hpo_tr wx x y P1 Pxy)].
            left. apply (Htr wx x y I1 Ix Iy G1).
            apply (Hr2 x y b Ix Iy Rx Ry Tx Ty Pxy).
            - intros [w [Iw [Ww [Tw [Pxw Pwy]]]]].
              assert (G1w : gmo wx w) by exact (Htr wx x w I1 Ix Iw G1 (Hr1 x w b Ix Iw Pxw Tx Tw Ww)).
              destruct (max_of_C4 y wy w Ry Iy Hs2 Iw Ww Tw (or_intror Pwy)) as [E1 | G2].
              + subst w. apply (Hirr wx I1). exact (Htr wx wy wx I1 I2 I1 G1w G).
              + apply (Hirr wx I1).
                exact (Htr wx wy wx I1 I2 I1 (Htr wx w wy I1 Iw I2 G1w G2) G).
            - intros [w [Hw1 Hw2]]. apply Hne.
              rewrite <- (Hrf_fun w wx b x Hw1 Hs1). exact (Hrf_fun w wy b y Hw2 Hs2). }
          destruct (max_of_C4 y wy wx Ry Iy Hs2 I1 W1 T1 Hc) as [E1 | G2].
          -- exact (Hne E1).
          -- apply (Hirr wx I1). exact (Htr wx wy wx I1 I2 I1 G2 G).
      + (* read, write *)
        rewrite (Src_write y wy Wy Sy). left.
        exact (read_then_write x y wx Ix Iy Rx Wy Tx Ty Pxy (Src_read x wx Rx Sx)).
      + (* write, read *)
        rewrite (Src_write x wx Wx Sx).
        pose proof (Src_read y wy Ry Sy) as Hs2.
        destruct (max_of_C4 y wy x Ry Iy Hs2 Ix Wx Tx (or_intror Pxy)) as [E1 | G].
        * right. split; [exact E1 |]. split; [exact Ry | left; exact Wx].
        * left; exact G.
      + (* write, write *)
        rewrite (Src_write x wx Wx Sx), (Src_write y wy Wy Sy). left.
        exact (Hr1 x y b Ix Iy Pxy Tx Ty Wy).
  Qed.

  Lemma inv_trans : forall x y z, Inv x y -> Inv y z -> (exists wy, Src y wy) -> Inv x z.
  Proof.
    intros x y z H1 H2 [wy Sy] wx wz Sx Sz.
    pose proof (Src_in x wx Sx) as Ix. pose proof (Src_in y wy Sy) as Iy.
    pose proof (Src_in z wz Sz) as Iz.
    destruct (H1 wx wy Sx Sy) as [G1 | [E1 [Ry O1]]];
      destruct (H2 wy wz Sy Sz) as [G2 | [E2 [Rz O2]]].
    - left. exact (Htr wx wy wz Ix Iy Iz G1 G2).
    - left. rewrite <- E2. exact G1.
    - left. rewrite E1. exact G2.
    - right. split; [rewrite E1; exact E2 |]. split; [exact Rz |].
      destruct O2 as [Wy | Pyz]; [exfalso; exact (Hrw y Ry Wy) |].
      destruct O1 as [Wx | Pxy]; [left; exact Wx | right; exact (Hpo_tr x y z Pxy Pyz)].
  Qed.

  Lemma path_inv : forall x y, clos_trans Event PB x y ->
      Inv x y /\ (exists wx, Src x wx) /\ (exists wy, Src y wy).
  Proof.
    intros x y H. induction H as [x y Hxy | x y z _ [I1 [S1 S2]] _ [I2 [_ S3]]].
    - destruct (edge_src x y Hxy) as [S1 S2]. split; [exact (edge_inv x y Hxy) |]. auto.
    - split; [exact (inv_trans x y z I1 I2 S2) |]. auto.
  Qed.

  Theorem rvwmo_perbyte_coherence : forall x, ~ clos_trans Event PB x x.
  Proof.
    intros x H. destruct (path_inv x x H) as [Hinv [[wx Sx] _]].
    destruct (Hinv wx wx Sx Sx) as [G | [_ [Rx [Wx | Pxx]]]].
    - exact (Hirr wx (Src_in x wx Sx) G).
    - exact (Hrw x Rx Wx).
    - exact (Hpo_irr x Pxx).
  Qed.

End RVWMOPerByte.

(* ==================================================================================================
   (4) Theorem 1 with the per-byte check
   ================================================================================================== *)

Section MLT1PerByte.

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

  Hypothesis Hirr : forall e, In e E0 -> ~ gmo e e.
  Hypothesis Htr  : forall a b c, In a E0 -> In b E0 -> In c E0 -> gmo a b -> gmo b c -> gmo a c.
  Hypothesis Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.
  Hypothesis Hpo_trans : forall a b c, po a b -> po b c -> po a c.
  Hypothesis rf_is_C4 : forall b r w, is_read r -> In r E0 -> rf w b r ->
      L1_abstract_erasure.C4_source Event Byte is_write touches gmo po E0 b r w.
  Hypothesis rf_touches : forall w b r, rf w b r -> touches w b.
  Hypothesis rf_functional : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.
  Hypothesis Hlanes : forall k d, In (k, d) LS ->
    ML_T1.LaneOK Event Byte Hart Value gmo is_write is_read touches wval addr data hart E0 rf po k d.
  Hypothesis keeper_survives : forall k d, In (k, d) LS -> ~ ML_T1.isdelL Event LS k.

  Definition tch_at (b : Byte) := touches_at Event Byte touches b.
  Definition rf_at' (b : Byte) := rf_at Event Byte rf b.
  Definition poloc_at' (b : Byte) := poloc_at Event Byte touches poloc b.

  (* the fault run's per-byte check, and the witness's *)
  Definition CfF_at (b : Byte) : Event -> Event -> Prop :=
    CfB Event Byte gmo is_write is_read touches E0 rf poloc b.
  Definition Cn_L_at (b : Byte) : Event -> Event -> Prop :=
    ML_T1.Cn_L Event Byte gmo is_write is_read (tch_at b) E0 (rf_at' b) (poloc_at' b) LS.

  (* every lane premise survives the restriction to one byte *)
  Lemma LaneOK_at : forall b k d,
      ML_T1.LaneOK Event Byte Hart Value gmo is_write is_read touches wval addr data hart E0 rf po k d ->
      ML_T1.LaneOK Event Byte Hart Value gmo is_write is_read (tch_at b) wval addr data hart E0
        (rf_at' b) po k d.
  Proof.
    intros b k d L.
    destruct L as [Lk Ld Wk Wd Gkd Pkd Hh Lfoot Lval Ladj Ltwin Lr12].
    constructor; try assumption.
    - intros b' [E1 T]. split; [exact E1 | apply Lfoot; exact T].
    - intros b' [_ T]. apply Lval; exact T.
    - intros b' [_ T] w Iw Ww [_ Tw]. exact (Ladj b' T w Iw Ww Tw).
    - intros a c x Ra [_ Ta] [_ Td] Pad Pdc. exact (Ltwin a c x Ra Ta Td Pad Pdc).
    - intros a c bb Pak Pkc Hdep [_ Hrf]. exact (Lr12 a c bb Pak Pkc Hdep Hrf).
  Qed.

  Lemma rf_touches_at : forall b w b' r, rf_at' b w b' r -> tch_at b w b'.
  Proof. intros b w b' r [E1 H]. split; [exact E1 | exact (rf_touches w b' r H)]. Qed.

  Theorem ML_witness_perbyte_acyclic :
    (forall b x, ~ clos_trans Event (CfF_at b) x x) ->
    forall b x, ~ clos_trans Event (Cn_L_at b) x x.
  Proof.
    intros Hpb b.
    exact (ML_T1.ML_witness_perloc_acyclic Event Byte Hart Value gmo is_write is_read (tch_at b) wval
             addr data hart E0 (rf_at' b) po (poloc_at' b) LS Htot (rf_touches_at b)
             (fun k d H => LaneOK_at b k d (Hlanes k d H)) (Hpb b)).
  Qed.

  Theorem ML_T1_refinement_pb :
    (forall b x, ~ clos_trans Event (CfB Event Byte gmo is_write is_read touches E0 rf poloc b) x x) ->
    (forall x, ~ clos_trans Event
       (Frozen_mainmodel.FRf Event Byte Hart gmo is_write is_read is_load is_store touches
          same_addr addr data ctrl fence hart E0 rf po) x x) ->
    exists (E_N : list Event) (rf_N : Event -> Byte -> Event -> Prop),
      E_N = ML_base.carrier_L Event eq_ev_dec E0 LS /\
      rf_N = ML_base.rf_L Event LS Byte rf /\
      (* (i)  per-byte check of the witness, at every byte *)
      (forall b x, ~ clos_trans Event (Cn_L_at b) x x) /\
      (* (ii) main-model check of the witness *)
      (forall x, ~ clos_trans Event
         (ML_T1.Rn_L Event Byte Hart gmo is_write is_read is_load is_store touches same_addr addr
            data ctrl fence hart E0 rf po LS) x x) /\
      (* (iii) the load-value rule of the witness over its carrier *)
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
    intros Hpb Hfrf.
    exists (ML_base.carrier_L Event eq_ev_dec E0 LS), (ML_base.rf_L Event LS Byte rf).
    split; [reflexivity |]. split; [reflexivity |].
    split; [exact (ML_witness_perbyte_acyclic Hpb) |].
    split; [exact (ML_T1.ML_witness_mainmodel_acyclic Event eq_ev_dec Byte Hart Value gmo is_write
                     is_read is_load is_store touches wval same_addr addr data ctrl fence hart E0 rf po
                     LS Htot rf_touches rf_functional Hlanes keeper_survives Hfrf) |].
    split; [exact (ML_T1.ML_erasure_preserves_consistency Event eq_ev_dec Byte Hart Value gmo is_write
                     is_read touches wval addr data hart E0 rf po LS Hirr Htr Htot Hpo_trans rf_is_C4
                     Hlanes keeper_survives) |].
    split.
    - intros r b w _ _ Hrf.
      exact (ML_T1.ML_erasure_preserves_read_values Event eq_ev_dec Byte Hart Value gmo is_write
               is_read touches wval addr data hart E0 rf po LS rf_touches rf_functional Hlanes r b w Hrf).
    - exact (ML_T1.ML_final_state_preserved_exists Event eq_ev_dec Byte Hart Value gmo is_write is_read
               touches wval addr data hart E0 rf po LS Htot Hlanes keeper_survives).
  Qed.

  (* every run that the union-graph theorem covers, the per-byte theorem covers *)
  Corollary ML_T1_pb_covers_union :
    (forall x, ~ clos_trans Event
       (Clift_coherence.Cf Event Byte gmo is_write is_read touches E0 rf poloc) x x) ->
    forall b x, ~ clos_trans Event (CfB Event Byte gmo is_write is_read touches E0 rf poloc b) x x.
  Proof. exact (union_to_perbyte Event Byte gmo is_write is_read touches E0 rf poloc). Qed.

End MLT1PerByte.

(* ==================================================================================================
   (5) the Stage-2 capstone with the per-byte check
   ================================================================================================== *)

Section MLStage2PerByte.

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte Hart Value Lane : Type.
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
  Variable Ctx : Event -> Prop.
  Variable ctx_dec : forall e, {Ctx e} + {~ Ctx e}.
  Variable is_chk : Event -> Prop.
  Variable chk_dec : forall e, {is_chk e} + {~ is_chk e}.
  Variable lane : Event -> Lane.
  Variable is_lane_write : Event -> Prop.
  Variable lanes : list Lane.

  Hypothesis Hirr : forall e, In e E0 -> ~ gmo e e.
  Hypothesis Htr : forall a b c, In a E0 -> In b E0 -> In c E0 -> gmo a b -> gmo b c -> gmo a c.
  Hypothesis Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.
  Hypothesis Hpo_trans : forall a b c, po a b -> po b c -> po a c.
  Hypothesis Hrf_is_C4 : forall b r w, is_read r -> In r E0 -> rf w b r ->
      L1_abstract_erasure.C4_source Event Byte is_write touches gmo po E0 b r w.
  Hypothesis Hrf_touches : forall w b r, rf w b r -> touches w b.
  Hypothesis Hrf_functional : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.
  Hypothesis Hlanes : forall k d, In (k, d) LS ->
    ML_T1.LaneOK Event Byte Hart Value gmo is_write is_read touches wval addr data hart E0 rf po k d.
  Hypothesis Hkeeper_survives : forall k d, In (k, d) LS -> ~ ML_base.isdel Event LS k.

  (* THE TWO CONSISTENCY ANTECEDENTS: per byte, and the main model *)
  Hypothesis Hfault_pb :
    forall b x, ~ clos_trans Event (CfB Event Byte gmo is_write is_read touches E0 rf poloc b) x x.
  Hypothesis Hfault_main :
    forall x, ~ clos_trans Event
      (Frozen_mainmodel.FRf Event Byte Hart gmo is_write is_read is_load is_store touches
         same_addr addr data ctrl fence hart E0 rf po) x x.

  Hypothesis Hrf_src_write : forall w b r, rf w b r -> is_write w.
  Hypothesis Hrf_tgt_read : forall w b r, rf w b r -> is_read r.
  Hypothesis Hpoloc_touches : forall x y, poloc x y -> exists b, touches x b /\ touches y b.
  Hypothesis Hctx_silent :
    forall e, Ctx e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b).
  Hypothesis Hchk_nonmem :
    forall e, is_chk e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b).

  Definition E_C := ML_stage2.E_C Event eq_ev_dec E0 LS.
  Definition E_K := ML_stage2.E_K Event eq_ev_dec E0 LS Ctx ctx_dec.
  Definition E_MK := Stage2_normal_candidate.mem_kernel Event E_K is_chk chk_dec.
  Definition E_N := Stage2_normal_candidate.EN' Event Lane E_K is_chk chk_dec lanes.
  Definition survC := ML_base.survivor_L Event E0 LS.
  Definition rf_C := ML_base.rf_L Event LS Byte rf.

  (* the per-byte relations at each carrier of the chain *)
  Definition rf_C_at (b : Byte) := ML_base.rf_L Event LS Byte (rf_at Event Byte rf b).
  Definition Cn_at (b : Byte) (C : Event -> Prop) :=
    CnC Event Byte gmo (poloc_at Event Byte touches poloc b) is_read is_write
      (touches_at Event Byte touches b) (rf_C_at b) C.
  Definition Cn_N_at (b : Byte) :=
    CnC (Stage2_normal_candidate.NEv Event Lane) Byte
      (Stage2_normal_candidate.gmo_N Event Lane gmo)
      (Stage2_normal_candidate.poloc_N Event Lane (poloc_at Event Byte touches poloc b))
      (Stage2_normal_candidate.is_read_N Event Lane is_read)
      (Stage2_normal_candidate.is_write_N Event Lane is_write)
      (Stage2_normal_candidate.touches_N Event Byte Lane (touches_at Event Byte touches b))
      (Stage2_normal_candidate.rf_N Event Byte Lane (rf_C_at b))
      (fun z => In z E_N).

  Definition ppow_C : Event -> Event -> Prop :=
    ML_T1.ppo_wit_L Event Byte is_write is_read is_load is_store touches same_addr addr data ctrl
      fence E0 rf po LS.
  Definition Rn_at (C : Event -> Prop) :=
    RnC Event Byte Hart gmo is_read is_write touches hart rf_C ppow_C C.
  Definition Rn_N :=
    RnC (Stage2_normal_candidate.NEv Event Lane) Byte (option Hart)
      (Stage2_normal_candidate.gmo_N Event Lane gmo)
      (Stage2_normal_candidate.is_read_N Event Lane is_read)
      (Stage2_normal_candidate.is_write_N Event Lane is_write)
      (Stage2_normal_candidate.touches_N Event Byte Lane touches)
      (hart_N Event Hart Lane hart)
      (Stage2_normal_candidate.rf_N Event Byte Lane rf_C)
      (ppo_N Event Lane ppow_C)
      (fun z => In z E_N).

  Lemma in_EC_surv : forall e, In e E_C -> survC e.
  Proof. exact (ML_stage2.in_EC_surv Event eq_ev_dec E0 LS). Qed.

  Lemma rfC_at_src_write : forall b w b' r, rf_C_at b w b' r -> is_write w.
  Proof.
    intros b w b' r H. destruct H as [[[_ H1] _] | [d [Hl _]]].
    - exact (Hrf_src_write w b' r H1).
    - exact (ML_T1.lk_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Hlanes w d Hl)).
  Qed.

  Lemma rfC_at_tgt_read : forall b w b' r, rf_C_at b w b' r -> is_read r.
  Proof.
    intros b w b' r H. destruct H as [[[_ H1] _] | [d [_ [_ H1]]]].
    - exact (Hrf_tgt_read w b' r H1).
    - exact (Hrf_tgt_read d b' r H1).
  Qed.

  Lemma silent_at : forall b P, (forall e, P e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b)) ->
      forall e, P e -> (~ is_read e) /\ (~ is_write e) /\
                       (forall b', ~ touches_at Event Byte touches b e b').
  Proof.
    intros b P H e Pe. destruct (H e Pe) as [R [W T]].
    split; [exact R |]. split; [exact W |]. intros b' [_ Tb]. exact (T b' Tb).
  Qed.

  Lemma poloc_at_touches : forall b x y, poloc_at Event Byte touches poloc b x y ->
      exists b', touches_at Event Byte touches b x b' /\ touches_at Event Byte touches b y b'.
  Proof.
    intros b x y [_ [Tx Ty]]. exists b. split; split; auto.
  Qed.

  (* ---- the per-byte check along the chain ---- *)

  Lemma Cn_C_at_acyclic : forall b x, ~ clos_trans Event (Cn_at b (fun e => In e E_C)) x x.
  Proof.
    intro b.
    apply (acyclic_sub Event (Cn_L_at Event Byte gmo is_write is_read touches E0 rf poloc LS b)).
    - intros x y H.
      exact (CnC_mono Event Byte gmo (poloc_at Event Byte touches poloc b) is_read is_write
               (touches_at Event Byte touches b) (rf_C_at b) survC (fun e => In e E_C)
               in_EC_surv x y H).
    - exact (ML_witness_perbyte_acyclic Event Byte Hart Value gmo is_write is_read touches wval addr
               data hart E0 rf po poloc LS Htot Hrf_touches Hlanes Hfault_pb b).
  Qed.

  Lemma Cn_C_K_at : forall b x y,
      Cn_at b (fun e => In e E_C) x y <-> Cn_at b (fun e => In e E_K) x y.
  Proof.
    intro b.
    exact (CnC_erase_iff Event Byte gmo (poloc_at Event Byte touches poloc b) is_read is_write
             (touches_at Event Byte touches b) (rf_C_at b) E_C Ctx ctx_dec
             (silent_at b Ctx Hctx_silent) (poloc_at_touches b)
             (rfC_at_src_write b) (rfC_at_tgt_read b)).
  Qed.

  Lemma Cn_K_MK_at : forall b x y,
      Cn_at b (fun e => In e E_K) x y <-> Cn_at b (fun e => In e E_MK) x y.
  Proof.
    intro b.
    exact (CnC_erase_iff Event Byte gmo (poloc_at Event Byte touches poloc b) is_read is_write
             (touches_at Event Byte touches b) (rf_C_at b) E_K is_chk chk_dec
             (silent_at b is_chk Hchk_nonmem) (poloc_at_touches b)
             (rfC_at_src_write b) (rfC_at_tgt_read b)).
  Qed.

  Lemma Cn_MK_at_acyclic : forall b x, ~ clos_trans Event (Cn_at b (fun e => In e E_MK)) x x.
  Proof.
    intro b. apply (acyclic_sub Event (Cn_at b (fun e => In e E_C))).
    - intros x y H. apply Cn_C_K_at. apply Cn_K_MK_at. exact H.
    - exact (Cn_C_at_acyclic b).
  Qed.

  Theorem Cn_N_at_acyclic :
    forall b n, ~ clos_trans (Stage2_normal_candidate.NEv Event Lane) (Cn_N_at b) n n.
  Proof.
    intro b.
    exact (CnN_acyclic Event Byte Lane gmo (poloc_at Event Byte touches poloc b) is_read is_write
             (touches_at Event Byte touches b) (rf_C_at b) E_K is_chk chk_dec lanes
             (Cn_MK_at_acyclic b)).
  Qed.

  (* ---- the main-model check along the chain (no per-location antecedent used) ---- *)

  Lemma Rn_C_acyclic : forall x, ~ clos_trans Event (Rn_at (fun e => In e E_C)) x x.
  Proof.
    apply (acyclic_sub Event
             (ML_T1.Rn_L Event Byte Hart gmo is_write is_read is_load is_store touches same_addr addr
                data ctrl fence hart E0 rf po LS)).
    - intros x y H.
      exact (proj1 (ML_stage2.Rn_C_is_ML_Rn Event eq_ev_dec Byte Hart gmo is_write is_read is_load
                      is_store touches same_addr addr data ctrl fence hart E0 rf po LS x y) H).
    - exact (ML_T1.ML_witness_mainmodel_acyclic Event eq_ev_dec Byte Hart Value gmo is_write is_read
               is_load is_store touches wval same_addr addr data ctrl fence hart E0 rf po LS Htot
               Hrf_touches Hrf_functional Hlanes Hkeeper_survives Hfault_main).
  Qed.

  Theorem Rn_N_acyclic :
    forall n, ~ clos_trans (Stage2_normal_candidate.NEv Event Lane) Rn_N n n.
  Proof.
    apply (RnN_acyclic Event Byte Hart Lane gmo is_read is_write touches hart rf_C ppow_C
             E_K is_chk chk_dec lanes).
    apply (acyclic_sub Event (Rn_at (fun e => In e E_C))).
    - intros x y H.
      apply (RnC_erase_sub Event Byte Hart gmo is_read is_write touches hart rf_C ppow_C
               E_C Ctx ctx_dec).
      apply (RnC_erase_sub Event Byte Hart gmo is_read is_write touches hart rf_C ppow_C
               E_K is_chk chk_dec).
      exact H.
    - exact Rn_C_acyclic.
  Qed.

  (* ---- the observation along the chain ---- *)

  Lemma pb_L1_consistent :
    L1_abstract_erasure.L1_consistent Event Byte is_write is_read touches gmo po E_C rf_C.
  Proof.
    exact (ML_T1.ML_erasure_preserves_consistency Event eq_ev_dec Byte Hart Value gmo is_write is_read
             touches wval addr data hart E0 rf po LS Hirr Htr Htot Hpo_trans Hrf_is_C4 Hlanes
             Hkeeper_survives).
  Qed.

  Lemma pb_read_values :
    forall r b w, rf w b r -> exists w', rf_C w' b r /\ wval w' b = wval w b.
  Proof.
    exact (ML_T1.ML_erasure_preserves_read_values Event eq_ev_dec Byte Hart Value gmo is_write is_read
             touches wval addr data hart E0 rf po LS Hrf_touches Hrf_functional Hlanes).
  Qed.

  Lemma pb_final_state :
    forall b w_f,
      Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E0) b w_f ->
      exists w_n, Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E_C) b w_n
                  /\ wval w_f b = wval w_n b.
  Proof.
    intros b w_f H.
    destruct (ML_T1.ML_final_state_preserved_exists Event eq_ev_dec Byte Hart Value gmo is_write is_read
                touches wval addr data hart E0 rf po LS Htot Hlanes Hkeeper_survives b w_f H)
      as [w_n [Hmax Hval]].
    exists w_n. split; [| exact Hval].
    apply (co_max_of_ext Event Byte gmo is_write touches survC (fun e => In e E_C)
             (fun e => iff_sym (ML_base.survivor_carrier Event eq_ev_dec E0 LS e)) b w_n Hmax).
  Qed.

  (* ================================================================================================
     HEADLINE: the Stage-2 chain with the per-byte check
     ================================================================================================ *)

  Theorem ML_stage2_endtoend_pb :
    (* the carriers nest; every replay is gone; the kernel is trap-free *)
    ((forall e, In e E_C -> In e E0)
     /\ (forall k d, In (k, d) LS -> ~ In d E_C)
     /\ (forall e, In e E_K -> In e E_C)
     /\ (forall e, In e E_MK -> In e E_K)
     /\ (forall e, In (Stage2_normal_candidate.NKeep Event Lane e) E_N <-> In e E_MK)
     /\ (forall e, In e E_K -> ~ Ctx e))
    (* the load-value rule and both halves of the observation at E_C *)
    /\ L1_abstract_erasure.L1_consistent Event Byte is_write is_read touches gmo po E_C rf_C
    /\ (forall r b w, rf w b r -> exists w', rf_C w' b r /\ wval w' b = wval w b)
    /\ (forall b w_f,
          Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E0) b w_f ->
          exists w_n,
            Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E_C) b w_n
            /\ wval w_f b = wval w_n b)
    (* both RVWMO checks at E_C and at the normal candidate; the per-location one per byte *)
    /\ (forall b x, ~ clos_trans Event (Cn_at b (fun e => In e E_C)) x x)
    /\ (forall x, ~ clos_trans Event (Rn_at (fun e => In e E_C)) x x)
    /\ (forall b n, ~ clos_trans (Stage2_normal_candidate.NEv Event Lane) (Cn_N_at b) n n)
    /\ (forall n, ~ clos_trans (Stage2_normal_candidate.NEv Event Lane) Rn_N n n)
    (* the byte-wise memory projection into the normal candidate *)
    /\ (forall b w,
          Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E_C) b w
          <-> Obs_final_state.co_max_of (Stage2_normal_candidate.NEv Event Lane) Byte
                (Stage2_normal_candidate.gmo_N Event Lane gmo)
                (Stage2_normal_candidate.is_write_N Event Lane is_write)
                (Stage2_normal_candidate.touches_N Event Byte Lane touches)
                (fun n => In n E_N) b (Stage2_normal_candidate.NKeep Event Lane w)).
  Proof.
    split.
    { split; [exact (ML_stage2.E_C_sub_E0 Event eq_ev_dec E0 LS) |].
      split; [exact (ML_stage2.E_C_no_replay Event eq_ev_dec E0 LS) |].
      split; [exact (ML_stage2.E_K_sub_E_C Event eq_ev_dec E0 LS Ctx ctx_dec) |].
      split; [exact (ML_stage2.E_MK_sub_E_K Event eq_ev_dec E0 LS Ctx ctx_dec is_chk chk_dec) |].
      split; [exact (ML_stage2.E_N_NKeep_iff Event eq_ev_dec Lane E0 LS Ctx ctx_dec is_chk chk_dec lanes) |].
      exact (ML_stage2.E_K_trap_free Event eq_ev_dec E0 LS Ctx ctx_dec). }
    split; [exact pb_L1_consistent |].
    split; [exact pb_read_values |].
    split; [exact pb_final_state |].
    split; [exact Cn_C_at_acyclic |].
    split; [exact Rn_C_acyclic |].
    split; [exact Cn_N_at_acyclic |].
    split; [exact Rn_N_acyclic |].
    exact (ML_stage2.endtoend_co_max Event eq_ev_dec Byte Lane gmo is_write is_read touches E0 LS Ctx
             ctx_dec is_chk chk_dec lanes Hctx_silent Hchk_nonmem).
  Qed.

End MLStage2PerByte.
