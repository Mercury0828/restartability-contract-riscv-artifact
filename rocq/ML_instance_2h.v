(* ML_instance_2h.v — RESTART-V: the running example with a REMOTE reader.

   Same events, values, coherence and reads-from as ML_instance.v, but on three harts: hart 0 runs
   the faulting vse64.v (W0, K2, K3, the trap region Tr Xr, the replay F1 D2 D3), hart 1 is the
   reader (Rp, R2, R3), and hart 2 holds the initial writes. Program order is the rank order within
   a hart and relates no events of different harts, so every read takes its value from another hart
   (rfe). One byte stands for each lane. The file proves every premise of the per-byte Theorem 1
   (`Perbyte.ML_T1_refinement_pb`), of the per-byte Stage-2 chain (`Perbyte.ML_stage2_endtoend_pb`)
   with the PMP part (`ML_stage2.ML_stage2_endtoend`), and of the generation lemma
   (`Normal_instance.normal_instance`) for this run, and applies all of them.

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
Require Import RestartV.Ctx_erasure.
Require Import RestartV.Frozen_pmp.
Require Import RestartV.ML_base.
Require Import RestartV.ML_T1.
Require Import RestartV.ML_stage2.
Require Import RestartV.Perbyte.
Require Import RestartV.Normal_instance.
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

(* hart 0 runs the faulting store and its handler, hart 1 is the remote reader, hart 2 holds the
   initial writes; program order is the rank order within a hart *)
Definition hart (e : Ev) : nat :=
  match e with Rp | R2 | R3 => 1 | Wi2 | Wi3 => 2 | _ => 0 end.
Definition po  (a b : Ev) : Prop := rank a < rank b /\ hart a = hart b.
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
  - exact (proj1 Hpo).
  - destruct Hf.
  - destruct Ha.
  - destruct Hd.
  - destruct Hc.
  - destruct Hex as [m [_ [_ Ham]]]; destruct Ham.
  - destruct Hex as [m [bb [_ [_ [[Ha | Hd] _]]]]]; [destruct Ha | destruct Hd].
Qed.

Definition CfC := Clift_coherence.Cf Ev Lb gmo is_write is_read touches E0 rf poloc.
Definition FRfC :=
  Frozen_mainmodel.FRf Ev Lb nat gmo is_write is_read is_read is_write
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
  - exact (proj1 Hpo).
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
      destruct Hr2 as [[_ [_ [_ [_ [Hpo _]]]]] _]. exact (proj1 Hpo).
Qed.

Definition Hcf  : forall x, ~ clos_trans Ev CfC  x x := acyc_from_rank CfC  edge_Cf.
Definition Hfrf : forall x, ~ clos_trans Ev FRfC x x := acyc_from_rank FRfC edge_FRf.

(* ============================ the premises, discharged ============================ *)

Lemma h_potrans : forall a b c, po a b -> po b c -> po a c.
Proof. unfold po; intros a b c [H1 H2] [H3 H4]; split; [lia | congruence]. Qed.

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
  ML_T1.LaneTok Ev Lb nat nat gmo is_write is_read touches wval addr data hart E0 rf po k d.
Proof.
  intros k d H. unfold LS in H. simpl in H.
  destruct H as [E | [E | []]]; inversion E; subst;
  (constructor;
  [ apply all_in_E0 | apply all_in_E0 | exact I | exact I
  | unfold gmo; simpl; lia | unfold po; simpl; split; [lia | reflexivity] | reflexivity
  | intros b H; exact H
  | intros b _; reflexivity
  | intros b Tdb w _ Ww Tw [G1 G2]; destruct b; simpl in Tdb; try contradiction;
      destruct w; simpl in Ww, Tw; try contradiction; unfold gmo in *; simpl in *; lia
  | intros e Hne Hpo; unfold po in *; destruct e; simpl in *; try lia;
      exfalso; apply Hne; reflexivity
  | intros a x Ra Tax Tdx [G1 G2]; destruct x; simpl in Tdx; try contradiction;
      destruct a; simpl in Ra, Tax; try contradiction; unfold po in *; simpl in *; lia
  | intros e; split; intro H; destruct H
  | intros bb c Hkc Hrf; destruct bb, c; simpl in Hrf; try contradiction;
      unfold po in Hkc; simpl in Hkc; destruct Hkc as [_ Hh]; discriminate Hh ]).
Qed.

Lemma h_keep : forall k d, In (k, d) LS -> ~ ML_base.isdel Ev LS k.
Proof.
  intros k d H. unfold LS in H. simpl in H.
  unfold ML_base.isdel, ML_base.dels, LS. simpl.
  destruct H as [E | [E | []]]; inversion E; subst;
    intros [X | [X | []]]; discriminate X.
Qed.


(* ============================ the Stage-2 data (as in ML_instance_stage2.v) ============================ *)

Definition Ctx (e : Ev) : Prop := e = Tr \/ e = Xr.

Definition ctx_dec : forall e, {Ctx e} + {~ Ctx e}.
Proof.
  intro e. unfold Ctx.
  destruct e;
    first [ left; left; reflexivity | left; right; reflexivity
          | right; intros [H | H]; discriminate H ].
Defined.

Definition is_chk (_ : Ev) : Prop := False.
Definition chk_dec : forall e, {is_chk e} + {~ is_chk e} := fun e => right (fun H => H).

Inductive Ln := ln0 | ln1 | ln2 | ln3.

Definition lane (e : Ev) : Ln :=
  match e with W0 => ln0 | F1 => ln1 | K2 | D2 => ln2 | K3 | D3 => ln3 | _ => ln0 end.
Definition is_lane_write (e : Ev) : Prop :=
  match e with W0 | F1 | K2 | K3 | D2 | D3 => True | _ => False end.
Definition lanes : list Ln := [ln0; ln1; ln2; ln3].
Definition lane_index (l : Ln) : nat := match l with ln0 => 0 | ln1 => 1 | ln2 => 2 | ln3 => 3 end.
Definition byte_addr (b : Lb) : nat := match b with L0 => 64 | L1 => 72 | L2 => 80 | L3 => 88 end.

(* the trap-free kernel: both replays and the trap region are gone *)
Lemma ml_kernel :
  Ctx_erasure.EK Ev (ML_base.carrier_L Ev ev_eq_dec E0 LS) Ctx ctx_dec =
  [Wi2; Wi3; Rp; W0; K2; K3; F1; R2; R3].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------- the Stage-2 premises *)

Lemma s_lanes : forall k d, In (k, d) LS ->
  ML_T1.LaneOK Ev Lb nat nat gmo is_write is_read touches wval addr data hart E0 rf po k d.
Proof.
  intros k d H.
  exact (ML_T1.LaneTok_LaneOK Ev Lb nat nat gmo is_write is_read touches wval addr data hart E0 rf
           po h_potrans h_rwdisj k d (h_lanes k d H)).
Qed.

Lemma s_rf_src : forall w b r, rf w b r -> is_write w.
Proof. intros w b r H. destruct w, b, r; simpl in H; try contradiction; exact I. Qed.

Lemma s_rf_tgt : forall w b r, rf w b r -> is_read r.
Proof. intros w b r H. destruct w, b, r; simpl in H; try contradiction; exact I. Qed.

Lemma s_poloc : forall x y, poloc x y -> exists b, touches x b /\ touches y b.
Proof. intros x y [_ H]. exact H. Qed.

Lemma s_ctx_silent :
  forall e, Ctx e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b).
Proof.
  intros e [E | E]; subst e;
    (split; [intro H; exact H | split; [intro H; exact H | intros b H; destruct b; exact H]]).
Qed.

Lemma s_chk_nonmem :
  forall e, is_chk e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b).
Proof. intros e H. destruct H. Qed.

Lemma s_K_lt : 1 < 4.
Proof. lia. Qed.

Lemma s_bg : forall i, i < 4 -> 0 <= Frozen_pmp.lane_lo 64 i /\ Frozen_pmp.lane_hi 64 i <= 1000.
Proof. intros i Hi. unfold Frozen_pmp.lane_lo, Frozen_pmp.lane_hi. lia. Qed.

Lemma s_nonempty : lanes <> nil.
Proof. discriminate. Qed.

Lemma s_complete : forall l : Ln, In l lanes.
Proof. intro l; destruct l; unfold lanes; simpl; tauto. Qed.

Lemma s_in_range : forall l, In l lanes -> lane_index l < 4.
Proof. intros l _; destruct l; simpl; lia. Qed.

Lemma s_cover : forall i, i < 4 -> exists l, In l lanes /\ lane_index l = i.
Proof.
  intros i Hi.
  destruct i as [| [| [| [| i]]]];
    [ exists ln0 | exists ln1 | exists ln2 | exists ln3 | lia ];
    (split; [apply s_complete | reflexivity]).
Qed.

Lemma s_inj : forall l1 l2, In l1 lanes -> In l2 lanes -> lane_index l1 = lane_index l2 -> l1 = l2.
Proof. intros l1 l2 _ _ H. destruct l1, l2; simpl in H; try reflexivity; discriminate H. Qed.

Lemma s_footprint : forall e l b,
  In e (Ctx_erasure.EK Ev (ML_base.carrier_L Ev ev_eq_dec E0 LS) Ctx ctx_dec) ->
  is_lane_write e -> lane e = l ->
  (touches e b <->
     Frozen_pmp.lane_lo 64 (lane_index l) <= byte_addr b /\
     byte_addr b < Frozen_pmp.lane_hi 64 (lane_index l)).
Proof.
  intros e l b _ Hw Hl. unfold Frozen_pmp.lane_lo, Frozen_pmp.lane_hi.
  destruct e; simpl in Hw; try contradiction; subst l;
    destruct b; simpl; split; intro H; first [ exact I | lia | contradiction ].
Qed.

Lemma s_one_write_per_lane : forall l, In l lanes ->
  exists w, In w (Ctx_erasure.EK Ev (ML_base.carrier_L Ev ev_eq_dec E0 LS) Ctx ctx_dec) /\
            is_lane_write w /\ lane w = l /\
            (forall w', In w' (Ctx_erasure.EK Ev (ML_base.carrier_L Ev ev_eq_dec E0 LS) Ctx ctx_dec) ->
                        is_lane_write w' -> lane w' = l -> w' = w).
Proof.
  intros l _. rewrite ml_kernel.
  destruct l; [exists W0 | exists F1 | exists K2 | exists K3];
    (split; [simpl; tauto |]); (split; [exact I |]); (split; [reflexivity |]);
    intros w' Hin Hw' Hl'; simpl in Hin;
    repeat (destruct Hin as [Hin | Hin]; [subst w'; simpl in Hw', Hl'; first
              [ reflexivity | contradiction | discriminate Hl' ] |]);
    destruct Hin.
Qed.

Lemma s_lane_write_is_write : forall e, is_lane_write e -> is_write e.
Proof. intros e H. destruct e; simpl in H; try contradiction; exact I. Qed.

(* the PMP part of the Stage-2 capstone, with the union-graph antecedent of this run *)
Definition ml2_stage2_instance :=
  ML_stage2.ML_stage2_endtoend
    Ev ev_eq_dec Lb nat nat Ln gmo is_write is_read is_read is_write touches wval
    same_addr addr data ctrl fence hart E0 rf po poloc LS Ctx ctx_dec is_chk chk_dec
    lane is_lane_write lanes
    h_Hirr h_Htr h_Htot h_potrans h_rfC4 h_rftouch h_rffun s_lanes h_keep Hcf Hfrf
    s_rf_src s_rf_tgt s_poloc s_ctx_silent s_chk_nonmem
    64 4 1 0 1000 lane_index byte_addr
    s_K_lt s_bg s_nonempty s_complete s_in_range s_cover s_inj s_footprint
    s_one_write_per_lane s_lane_write_is_write.

(* ============================ the per-byte theorems and the generation lemma ============================ *)

Definition Hpb2 : forall b x, ~ clos_trans Ev (CfB Ev Lb gmo is_write is_read touches E0 rf poloc b) x x :=
  union_to_perbyte Ev Lb gmo is_write is_read touches E0 rf poloc Hcf.

Definition ml2_T1_pb_instance :=
  Perbyte.ML_T1_refinement_pb Ev ev_eq_dec Lb nat nat gmo is_write is_read is_read is_write touches
    wval same_addr addr data ctrl fence hart E0 rf po poloc LS
    h_Hirr h_Htr h_Htot h_potrans h_rfC4 h_rftouch h_rffun s_lanes h_keep Hpb2 Hfrf.

Definition ml2_stage2_pb_instance :=
  Perbyte.ML_stage2_endtoend_pb Ev ev_eq_dec Lb nat nat Ln gmo is_write is_read is_read is_write
    touches wval same_addr addr data ctrl fence hart E0 rf po poloc LS Ctx ctx_dec is_chk chk_dec
    lanes h_Hirr h_Htr h_Htot h_potrans h_rfC4 h_rftouch h_rffun s_lanes h_keep Hpb2 Hfrf
    s_rf_src s_rf_tgt s_ctx_silent s_chk_nonmem.

(* ---------------------------------------------------------------- the generation premises *)

Definition vdata (l : Ln) (_ : Lb) : nat :=
  match l with ln0 => 4 | ln1 => 1 | ln2 => 5 | ln3 => 6 end.

Lemma n_value : forall e b,
  In e (Normal_instance.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec) -> is_lane_write e -> touches e b ->
  wval e b = vdata (lane e) b.
Proof. intros e b _ He _. destruct e; simpl in He; try contradiction; reflexivity. Qed.

Lemma n_po_hart : forall a b, po a b -> hart a = hart b.
Proof. intros a b [_ H]; exact H. Qed.

Lemma n_po_total : forall a b, In a E0 -> In b E0 -> hart a = hart b -> a <> b -> po a b \/ po b a.
Proof.
  intros a b _ _ Hh H. unfold po. rewrite Hh.
  destruct a, b; simpl; first [ left; split; [lia | reflexivity] | right; split; [lia | reflexivity]
                              | exfalso; apply H; reflexivity ].
Qed.

Lemma n_inst_hart : forall a b, is_lane_write a -> is_lane_write b -> hart a = hart b.
Proof. intros a b Ha Hb. destruct a; simpl in Ha; try contradiction; destruct b; simpl in Hb; try contradiction; reflexivity. Qed.

Lemma n_window : forall a x b, In x E0 -> is_lane_write a -> is_lane_write b ->
    po a x -> po x b -> is_lane_write x \/ Ctx x \/ is_chk x.
Proof.
  intros a x b _ Ha Hb [P1 _] [P2 _].
  destruct a; simpl in Ha; try contradiction; destruct b; simpl in Hb; try contradiction;
    destruct x; simpl in *; try lia;
    first [ left; exact I | right; left; unfold Ctx; auto ].
Qed.

Lemma n_deps : forall x a b,
    In x (Normal_instance.E_MK Ev ev_eq_dec E0 LS Ctx ctx_dec is_chk chk_dec) ->
    ~ is_lane_write x -> is_lane_write a -> is_lane_write b ->
    (addr x a <-> addr x b) /\ (data x a <-> data x b) /\ (ctrl x a <-> ctrl x b).
Proof. intros. unfold addr, data, ctrl. tauto. Qed.

Definition ml2_normal_instance :=
  Normal_instance.normal_instance Ev ev_eq_dec Lb nat nat Ln gmo is_write is_read is_read is_write
    touches wval same_addr addr data ctrl fence hart E0 rf po poloc LS Ctx ctx_dec is_chk chk_dec
    lane is_lane_write lanes vdata 64 lane_index byte_addr
    h_Htot h_rftouch h_rffun s_lanes h_keep Hpb2 Hfrf s_rf_src s_rf_tgt s_ctx_silent s_chk_nonmem
    h_rwdisj s_lane_write_is_write s_one_write_per_lane s_footprint n_value n_po_hart n_po_total
    n_inst_hart n_window n_deps.

(* ============================ what the two-hart instance shows ============================ *)

(* both remote reads sourced a deleted replay; after erasure they still see 5 and 6 *)
Lemma ml2_carrier : ML_base.carrier_L Ev ev_eq_dec E0 LS =
  [Wi2; Wi3; Rp; W0; K2; K3; Tr; Xr; F1; R2; R3].
Proof. reflexivity. Qed.

Lemma comax2_D2 : Obs_final_state.co_max_of Ev Lb gmo is_write touches
                   (Obs_final_state.inE0 Ev E0) L2 D2.
Proof.
  split; [exact I |]. split; [exact I |]. split; [apply all_in_E0 |].
  intros w' _ Ww' Tw'. destruct w'; simpl in Ww', Tw'; try contradiction;
    first [ left; reflexivity | right; unfold gmo; simpl; lia ].
Qed.

Lemma comax2_D3 : Obs_final_state.co_max_of Ev Lb gmo is_write touches
                   (Obs_final_state.inE0 Ev E0) L3 D3.
Proof.
  split; [exact I |]. split; [exact I |]. split; [apply all_in_E0 |].
  intros w' _ Ww' Tw'. destruct w'; simpl in Ww', Tw'; try contradiction;
    first [ left; reflexivity | right; unfold gmo; simpl; lia ].
Qed.

(* After erasing BOTH duplicates: the reads of lanes 2 and 3 still see 5 and 6, and the final values
   of lanes 2 and 3 are still 5 and 6. Both reads sourced a deleted write, so the theorem had to
   supply replacements for two lanes at once. *)
Theorem ml2_instance_observation :
  ML_base.carrier_L Ev ev_eq_dec E0 LS = [Wi2; Wi3; Rp; W0; K2; K3; Tr; Xr; F1; R2; R3] /\
  (exists w, ML_base.rf_L Ev LS Lb rf w L2 R2 /\ wval w L2 = 5) /\
  (exists w, ML_base.rf_L Ev LS Lb rf w L3 R3 /\ wval w L3 = 6) /\
  (exists w, Obs_final_state.co_max_of Ev Lb gmo is_write touches
               (ML_base.survivor_L Ev E0 LS) L2 w /\ wval w L2 = 5) /\
  (exists w, Obs_final_state.co_max_of Ev Lb gmo is_write touches
               (ML_base.survivor_L Ev E0 LS) L3 w /\ wval w L3 = 6).
Proof.
  destruct ml2_T1_pb_instance as
    [E_N [rf_N [HE [Hrf [_ [_ [_ [Hread Hcomax]]]]]]]].
  assert (HR2 : In R2 E_N) by (rewrite HE, ml2_carrier; simpl; tauto).
  assert (HR3 : In R3 E_N) by (rewrite HE, ml2_carrier; simpl; tauto).
  split; [exact ml2_carrier |].
  split; [| split; [| split]].
  - destruct (Hread R2 L2 D2 HR2 I I) as [w [Hw Hv]]. rewrite Hrf in Hw.
    exists w. split; [exact Hw | exact Hv].
  - destruct (Hread R3 L3 D3 HR3 I I) as [w [Hw Hv]]. rewrite Hrf in Hw.
    exists w. split; [exact Hw | exact Hv].
  - destruct (Hcomax L2 D2 comax2_D2) as [w [Hw Hv]]. exists w. split; [exact Hw | symmetry; exact Hv].
  - destruct (Hcomax L3 D3 comax2_D3) as [w [Hw Hv]]. exists w. split; [exact Hw | symmetry; exact Hv].
Qed.

