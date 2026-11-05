(* ML_instance.v — RESTART-V: non-vacuity of the general-lane theorem with TWO provisional lanes.

   `ML_T1.ML_T1_refinement_instantiated` is conditional on its premises. This file exhibits a concrete
   fault execution that satisfies every one of them, with |P| = 2, and applies the theorem to it.

   THE RUN. A `vse64.v` with VL = 4 faults at lane K = 1 (vstart = 1). The first attempt commits lane 0
   and, as the vector specification permits for idempotent memory, also writes lanes 2 and 3 before
   the trap: P = {2, 3}. The handler runs (two memory-silent trap-region events), and the replay from
   vstart writes lanes 1, 2 and 3. Lanes 2 and 3 are therefore written twice with equal values.

     rank  0 Wi2   initial write, lane-2 byte          7 Xr   mret (touches nothing)
           1 Wi3   initial write, lane-3 byte          8 F1   replay, lane 1 (the faulting lane, once)
           2 Rp    read of lane 2 before the store     9 D2   replay, lane 2   (deleted duplicate)
           3 W0    first attempt, lane 0 (committed)  10 D3   replay, lane 3   (deleted duplicate)
           4 K2    first attempt, lane 2 (keeper)     11 R2   read of lane 2 after the store
           5 K3    first attempt, lane 3 (keeper)     12 R3   read of lane 3 after the store
           6 Tr    M-mode handler (touches nothing)

   Program order and coherence are both the rank order: every first attempt precedes every replay.
   This is the NATURAL interleaving, in which K3 lies coherence-between K2 and D2. The per-byte
   erasure condition of each lane still holds, because K3 writes a different byte. The final lemma
   `natural_order_breaks_global_adj` records that the address-blind adjacency of Multi_lane.v does
   not hold on this run, which is why ML_T1 states γ_adj per byte.

   0 Admitted / 0 axioms. Modifies no existing .v file. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.micromega.Lia.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Rlift_mainmodel.
Require Import RestartV.PPO_union.
Require Import RestartV.Frozen_mainmodel.
Require Import RestartV.Obs_final_state.
Require Import RestartV.Multi_lane.
Require Import RestartV.ML_base.
Require Import RestartV.ML_T1.
Import ListNotations.

(* ============================ the concrete model ============================ *)

Inductive Ev := Wi2 | Wi3 | Rp | W0 | K2 | K3 | Tr | Xr | F1 | D2 | D3 | R2 | R3.
Inductive Lb := L0 | L1 | L2 | L3.          (* one byte per lane footprint *)

Definition ev_eq_dec : forall x y : Ev, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition rank (e : Ev) : nat :=
  match e with
  | Wi2 => 0 | Wi3 => 1 | Rp => 2 | W0 => 3 | K2 => 4 | K3 => 5 | Tr => 6
  | Xr => 7 | F1 => 8 | D2 => 9 | D3 => 10 | R2 => 11 | R3 => 12
  end.

Definition po  (a b : Ev) : Prop := rank a < rank b.
Definition gmo (a b : Ev) : Prop := rank a < rank b.

Definition is_write (e : Ev) : Prop :=
  match e with Wi2 | Wi3 | W0 | K2 | K3 | F1 | D2 | D3 => True | _ => False end.
Definition is_read (e : Ev) : Prop := match e with Rp | R2 | R3 => True | _ => False end.

Definition touches (e : Ev) (b : Lb) : Prop :=
  match e, b with
  | Wi2, L2 | Rp, L2 | K2, L2 | D2, L2 | R2, L2 => True
  | Wi3, L3 | K3, L3 | D3, L3 | R3, L3 => True
  | W0, L0 | F1, L1 => True
  | _, _ => False
  end.

Definition wval (e : Ev) (_ : Lb) : nat :=
  match e with K2 | D2 => 5 | K3 | D3 => 6 | W0 => 4 | F1 => 1 | _ => 0 end.

Definition hart (_ : Ev) : unit := tt.

Definition rf (w : Ev) (b : Lb) (r : Ev) : Prop :=
  match w, b, r with
  | Wi2, L2, Rp | D2, L2, R2 | D3, L3, R3 => True
  | _, _, _ => False
  end.

Definition addr (_ _ : Ev) : Prop := False.
Definition data (_ _ : Ev) : Prop := False.
Definition ctrl (_ _ : Ev) : Prop := False.
Definition fence (_ _ : Ev) : Prop := False.
Definition same_addr (a b : Ev) : Prop := exists x, touches a x /\ touches b x.
Definition poloc (a b : Ev) : Prop := po a b /\ same_addr a b.

Definition E0 : list Ev := [Wi2; Wi3; Rp; W0; K2; K3; Tr; Xr; F1; D2; D3; R2; R3].
Definition LS : list (Ev * Ev) := [(K2, D2); (K3, D3)].     (* P = {2, 3} *)

Ltac inE0tac := unfold E0; simpl; repeat (first [ left; reflexivity | right ]).

Lemma all_in_E0 : forall e, In e E0.
Proof. intro e; destruct e; inE0tac. Qed.

(* ============================ the two acyclicity certificates ============================ *)

Lemma ct_rank : forall (R : Ev -> Ev -> Prop),
  (forall x y, R x y -> rank x < rank y) ->
  forall x y, clos_trans Ev R x y -> rank x < rank y.
Proof. intros R Hedge x y Hct. induction Hct; [apply Hedge; assumption | lia]. Qed.

Lemma acyc_from_rank : forall (R : Ev -> Ev -> Prop),
  (forall x y, R x y -> rank x < rank y) -> forall x, ~ clos_trans Ev R x x.
Proof. intros R Hedge x Hct. pose proof (ct_rank R Hedge x x Hct). lia. Qed.

Lemma rf_rank : forall w b r, rf w b r -> rank w < rank r.
Proof. intros w b r H. destruct w, b, r; simpl in H; try contradiction; simpl; lia. Qed.

(* a from-reads edge goes up in rank: the read sits above its source, and the overwriting write
   at the same byte sits above the read *)
Lemma fr_rank : forall w1 b x y,
  rf w1 b x -> is_write y -> touches y b -> gmo w1 y -> rank x < rank y.
Proof.
  intros w1 b x y Hrf Hw Ht Hg. unfold gmo in Hg.
  destruct w1, b, x; simpl in Hrf; try contradiction;
    destruct y; simpl in Hw, Ht; try contradiction; simpl in *; lia.
Qed.

Lemma ppoF_rank : forall x y,
  PPO_union.ppoF Ev Lb po is_read is_write same_addr addr data ctrl fence rf x y -> rank x < rank y.
Proof.
  intros x y H.
  destruct H as [ a b Hpo Hsa Hst | a b Hf | a b Ha | a b Hd | a b Hc Hst
                | a b Hst Hex | a b Hlb Hex ].
  - exact Hpo.
  - destruct Hf.
  - destruct Ha.
  - destruct Hd.
  - destruct Hc.
  - destruct Hex as [m [_ [_ Ham]]]; destruct Ham.
  - destruct Hex as [m [bb [_ [_ [[Ha | Hd] _]]]]]; [destruct Ha | destruct Hd].
Qed.

Definition CfC := Clift_coherence.Cf Ev Lb gmo is_write is_read touches E0 rf poloc.
Definition FRfC :=
  Frozen_mainmodel.FRf Ev Lb unit gmo is_write is_read is_read is_write
    touches same_addr addr data ctrl fence hart E0 rf po.

Lemma edge_Cf : forall x y, CfC x y -> rank x < rank y.
Proof.
  intros x y H. unfold CfC, Clift_coherence.Cf in H.
  destruct H as [ [b Hco] | [ [b [Hrx Hfr]] | [ [b Hrf] | [Hpo _] ] ] ].
  - unfold Clift_coherence.co_flt, Clift_coherence.coOn in Hco.
    destruct Hco as [_ [_ [_ [_ [_ [_ G]]]]]]. exact G.
  - destruct Hfr as [w1 [Hrf Hco]].
    unfold Clift_coherence.co_flt, Clift_coherence.coOn in Hco.
    destruct Hco as [_ [_ [_ [Wy [_ [Ty G]]]]]].
    exact (fr_rank w1 b x y Hrf Wy Ty G).
  - exact (rf_rank x b y Hrf).
  - exact Hpo.
Qed.

Lemma edge_FRf : forall x y, FRfC x y -> rank x < rank y.
Proof.
  intros x y H. unfold FRfC, Frozen_mainmodel.FRf, Rlift_mainmodel.Rf in H.
  destruct H as [ [b Hco] | [ [b [Hrx Hfr]] | [ Hrfe | Hppo ] ] ].
  - unfold Rlift_mainmodel.co_flt, Rlift_mainmodel.coOn in Hco.
    destruct Hco as [_ [_ [_ [_ [_ [_ G]]]]]]. exact G.
  - destruct Hfr as [w1 [Hrf Hco]].
    unfold Rlift_mainmodel.co_flt, Rlift_mainmodel.coOn in Hco.
    destruct Hco as [_ [_ [_ [Wy [_ [Ty G]]]]]].
    exact (fr_rank w1 b x y Hrf Wy Ty G).
  - destruct Hrfe as [b [Hrf _]]. exact (rf_rank x b y Hrf).
  - unfold Frozen_mainmodel.fault_ppo in Hppo. destruct Hppo as [Hpf | [bx Hr2]].
    + exact (ppoF_rank x y Hpf).
    + unfold PPO_union.r2F, PPO_union.polnw_F in Hr2.
      destruct Hr2 as [[_ [_ [_ [_ [Hpo _]]]]] _]. exact Hpo.
Qed.

Definition Hcf  : forall x, ~ clos_trans Ev CfC  x x := acyc_from_rank CfC  edge_Cf.
Definition Hfrf : forall x, ~ clos_trans Ev FRfC x x := acyc_from_rank FRfC edge_FRf.

(* ============================ the premises, discharged ============================ *)

Lemma h_potrans : forall a b c, po a b -> po b c -> po a c.
Proof. unfold po; intros; lia. Qed.

Lemma h_rwdisj : forall e, is_read e -> is_write e -> False.
Proof. intros e Hr Hw. destruct e; simpl in Hr, Hw; contradiction. Qed.

Lemma h_Hirr : forall e, In e E0 -> ~ gmo e e.
Proof. unfold gmo; intros; lia. Qed.

Lemma h_Htr : forall a b c, In a E0 -> In b E0 -> In c E0 -> gmo a b -> gmo b c -> gmo a c.
Proof. unfold gmo; intros; lia. Qed.

Lemma h_Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.
Proof.
  intros a b _ _ Hne. unfold gmo.
  destruct a, b; simpl; try lia; exfalso; apply Hne; reflexivity.
Qed.

Lemma h_rfC4 : forall b r w, is_read r -> In r E0 -> rf w b r ->
  L1_abstract_erasure.C4_source Ev Lb is_write touches gmo po E0 b r w.
Proof.
  intros b r w Hr _ Hrf.
  unfold L1_abstract_erasure.C4_source, L1_abstract_erasure.cand.
  destruct w, b, r; simpl in Hrf; try contradiction;
    (split;
     [ split; [apply all_in_E0 |]; split; [exact I |]; split; [exact I |];
       left; unfold gmo; simpl; lia
     | intros w' [_ [Ww' [Tw' Ord]]];
       destruct w'; simpl in Ww', Tw'; try contradiction;
       unfold gmo, po in *; simpl in *;
       first [ left; reflexivity | right; lia | exfalso; destruct Ord; lia ] ]).
Qed.

Lemma h_rftouch : forall w b r, rf w b r -> touches w b.
Proof. intros w b r H. destruct w, b, r; simpl in H; try contradiction; exact I. Qed.

Lemma h_rffun : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.
Proof.
  intros w1 w2 x r H1 H2.
  destruct w1, x, r; simpl in H1; try contradiction;
    destruct w2; simpl in H2; try contradiction; reflexivity.
Qed.

Lemma h_lanes : forall k d, In (k, d) LS ->
  ML_T1.LaneTok Ev Lb unit nat gmo is_write is_read touches wval addr data hart E0 rf po k d.
Proof.
  intros k d H. unfold LS in H. simpl in H.
  destruct H as [E | [E | []]]; inversion E; subst;
  (constructor;
  [ apply all_in_E0 | apply all_in_E0 | exact I | exact I
  | unfold gmo; simpl; lia | unfold po; simpl; lia | reflexivity
  | intros b H; exact H
  | intros b _; reflexivity
  | intros b Tdb w _ Ww Tw [G1 G2]; destruct b; simpl in Tdb; try contradiction;
      destruct w; simpl in Ww, Tw; try contradiction; unfold gmo in *; simpl in *; lia
  | intros e Hne Hpo; unfold po in *; destruct e; simpl in *; try lia;
      exfalso; apply Hne; reflexivity
  | intros a x Ra Tax Tdx [G1 G2]; destruct x; simpl in Tdx; try contradiction;
      destruct a; simpl in Ra, Tax; try contradiction; unfold po in *; simpl in *; lia
  | intros e; split; intro H; destruct H
  | intros bb c _ Hrf; destruct bb, c; simpl in Hrf; try contradiction; unfold po; simpl; lia ]).
Qed.

Lemma h_keep : forall k d, In (k, d) LS -> ~ ML_base.isdel Ev LS k.
Proof.
  intros k d H. unfold LS in H. simpl in H.
  unfold ML_base.isdel, ML_base.dels, LS. simpl.
  destruct H as [E | [E | []]]; inversion E; subst;
    intros [X | [X | []]]; discriminate X.
Qed.

(* ============================ apply the general-lane theorem ============================ *)

Definition ml_concrete_instance :=
  ML_T1.ML_T1_refinement_instantiated
    Ev ev_eq_dec Lb unit nat gmo is_write is_read is_read is_write
    touches wval same_addr addr data ctrl fence hart E0 rf po poloc LS
    h_potrans h_rwdisj h_Hirr h_Htr h_Htot h_rfC4 h_rftouch h_rffun h_lanes h_keep
    Hcf Hfrf.

(* ============================ what the instance shows ============================ *)

(* Both replay duplicates leave the carrier; both keepers and every other event stay. *)
Lemma ml_carrier : ML_base.carrier_L Ev ev_eq_dec E0 LS =
  [Wi2; Wi3; Rp; W0; K2; K3; Tr; Xr; F1; R2; R3].
Proof. reflexivity. Qed.

Lemma comax_D2 : Obs_final_state.co_max_of Ev Lb gmo is_write touches
                   (Obs_final_state.inE0 Ev E0) L2 D2.
Proof.
  split; [exact I |]. split; [exact I |]. split; [apply all_in_E0 |].
  intros w' _ Ww' Tw'. destruct w'; simpl in Ww', Tw'; try contradiction;
    first [ left; reflexivity | right; unfold gmo; simpl; lia ].
Qed.

Lemma comax_D3 : Obs_final_state.co_max_of Ev Lb gmo is_write touches
                   (Obs_final_state.inE0 Ev E0) L3 D3.
Proof.
  split; [exact I |]. split; [exact I |]. split; [apply all_in_E0 |].
  intros w' _ Ww' Tw'. destruct w'; simpl in Ww', Tw'; try contradiction;
    first [ left; reflexivity | right; unfold gmo; simpl; lia ].
Qed.

(* After erasing BOTH duplicates: the reads of lanes 2 and 3 still see 5 and 6, and the final values
   of lanes 2 and 3 are still 5 and 6. Both reads sourced a deleted write, so the theorem had to
   supply replacements for two lanes at once. *)
Theorem ml_instance_observation :
  ML_base.carrier_L Ev ev_eq_dec E0 LS = [Wi2; Wi3; Rp; W0; K2; K3; Tr; Xr; F1; R2; R3] /\
  (exists w, ML_base.rf_L Ev LS Lb rf w L2 R2 /\ wval w L2 = 5) /\
  (exists w, ML_base.rf_L Ev LS Lb rf w L3 R3 /\ wval w L3 = 6) /\
  (exists w, Obs_final_state.co_max_of Ev Lb gmo is_write touches
               (ML_base.survivor_L Ev E0 LS) L2 w /\ wval w L2 = 5) /\
  (exists w, Obs_final_state.co_max_of Ev Lb gmo is_write touches
               (ML_base.survivor_L Ev E0 LS) L3 w /\ wval w L3 = 6).
Proof.
  destruct ml_concrete_instance as
    [E_N [rf_N [HE [Hrf [_ [_ [_ [Hread Hcomax]]]]]]]].
  assert (HR2 : In R2 E_N) by (rewrite HE, ml_carrier; simpl; tauto).
  assert (HR3 : In R3 E_N) by (rewrite HE, ml_carrier; simpl; tauto).
  split; [exact ml_carrier |].
  split; [| split; [| split]].
  - destruct (Hread R2 L2 D2 HR2 I I) as [w [Hw Hv]]. rewrite Hrf in Hw.
    exists w. split; [exact Hw | exact Hv].
  - destruct (Hread R3 L3 D3 HR3 I I) as [w [Hw Hv]]. rewrite Hrf in Hw.
    exists w. split; [exact Hw | exact Hv].
  - destruct (Hcomax L2 D2 comax_D2) as [w [Hw Hv]]. exists w. split; [exact Hw | symmetry; exact Hv].
  - destruct (Hcomax L3 D3 comax_D3) as [w [Hw Hv]]. exists w. split; [exact Hw | symmetry; exact Hv].
Qed.

(* The address-blind adjacency of Multi_lane.v fails on this natural run: K3 is a write lying
   coherence-between K2 and D2. The per-byte γ_adj that ML_T1 uses holds (h_lanes). *)
Lemma natural_order_breaks_global_adj :
  ~ Multi_lane.lanes_ok Ev ev_eq_dec Lb nat is_write touches wval gmo po LS E0.
Proof.
  unfold LS. simpl. intros [[_ [_ [_ [_ [_ [_ [_ Hadj]]]]]]] _].
  apply (Hadj K3); [apply all_in_E0 | exact I | discriminate | discriminate |].
  unfold gmo; simpl; lia.
Qed.
