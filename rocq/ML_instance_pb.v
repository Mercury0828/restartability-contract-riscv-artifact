(* ML_instance_pb.v — RESTART-V: the two-lane run of ML_instance.v inhabits every premise of the
   per-byte theorems and of the generation lemma, which are then applied to it.

   Same run and same Stage-2 data as ML_instance_stage2.v. The new premises:
     * the per-byte check of the fault run follows from its union check (`Perbyte.union_to_perbyte`);
     * program order is the rank order on one hart, so it is per hart and total on a hart;
     * the element writes W0 K2 K3 | F1 D2 D3 have between them only the trap region {Tr, Xr};
     * the run has no address, data or control dependencies;
     * the element values are 4, 1, 5, 6, those of the data register.

   0 Admitted / 0 axioms. Modifies no existing .v file. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.micromega.Lia.
Require Import RestartV.Ctx_erasure.
Require Import RestartV.Frozen_pmp.
Require Import RestartV.ML_base.
Require Import RestartV.ML_T1.
Require Import RestartV.ML_stage2.
Require Import RestartV.Perbyte.
Require Import RestartV.Normal_instance.
Require Import RestartV.ML_instance.
Require Import RestartV.ML_instance_stage2.
Import ListNotations.

Definition Hpb : forall b x, ~ clos_trans Ev (CfB Ev Lb gmo is_write is_read touches E0 rf poloc b) x x :=
  union_to_perbyte Ev Lb gmo is_write is_read touches E0 rf poloc Hcf.

Definition ml_T1_pb_instance :=
  Perbyte.ML_T1_refinement_pb Ev ev_eq_dec Lb unit nat gmo is_write is_read is_read is_write touches
    wval same_addr addr data ctrl fence hart E0 rf po poloc LS
    h_Hirr h_Htr h_Htot h_potrans h_rfC4 h_rftouch h_rffun s_lanes h_keep Hpb Hfrf.

Definition ml_stage2_pb_instance :=
  Perbyte.ML_stage2_endtoend_pb Ev ev_eq_dec Lb unit nat Ln gmo is_write is_read is_read is_write
    touches wval same_addr addr data ctrl fence hart E0 rf po poloc LS Ctx ctx_dec is_chk chk_dec
    lanes h_Hirr h_Htr h_Htot h_potrans h_rfC4 h_rftouch h_rffun s_lanes h_keep Hpb Hfrf
    s_rf_src s_rf_tgt s_ctx_silent s_chk_nonmem.

(* ---------------------------------------------------------------- the generation premises *)

Definition vdata (l : Ln) (_ : Lb) : nat :=
  match l with ln0 => 4 | ln1 => 1 | ln2 => 5 | ln3 => 6 end.

Lemma n_value : forall e b,
  In e (Normal_instance.E_K Ev ev_eq_dec E0 LS Ctx ctx_dec) -> is_lane_write e -> touches e b ->
  wval e b = vdata (lane e) b.
Proof. intros e b _ He _. destruct e; simpl in He; try contradiction; reflexivity. Qed.

Lemma n_po_hart : forall a b, po a b -> hart a = hart b.
Proof. intros; reflexivity. Qed.

Lemma n_po_total : forall a b, In a E0 -> In b E0 -> hart a = hart b -> a <> b -> po a b \/ po b a.
Proof.
  intros a b _ _ _ H. unfold po.
  destruct a, b; simpl; try lia; exfalso; apply H; reflexivity.
Qed.

Lemma n_inst_hart : forall a b, is_lane_write a -> is_lane_write b -> hart a = hart b.
Proof. intros; reflexivity. Qed.

Lemma n_window : forall a x b, In x E0 -> is_lane_write a -> is_lane_write b ->
    po a x -> po x b -> is_lane_write x \/ Ctx x \/ is_chk x.
Proof.
  intros a x b _ Ha Hb P1 P2. unfold po in *.
  destruct a; simpl in Ha; try contradiction; destruct b; simpl in Hb; try contradiction;
    destruct x; simpl in *; try lia;
    first [ left; exact I | right; left; unfold Ctx; auto ].
Qed.

Lemma n_deps : forall x a b,
    In x (Normal_instance.E_MK Ev ev_eq_dec E0 LS Ctx ctx_dec is_chk chk_dec) ->
    ~ is_lane_write x -> is_lane_write a -> is_lane_write b ->
    (addr x a <-> addr x b) /\ (data x a <-> data x b) /\ (ctrl x a <-> ctrl x b).
Proof. intros. unfold addr, data, ctrl. tauto. Qed.

Definition ml_normal_instance :=
  Normal_instance.normal_instance Ev ev_eq_dec Lb unit nat Ln gmo is_write is_read is_read is_write
    touches wval same_addr addr data ctrl fence hart E0 rf po poloc LS Ctx ctx_dec is_chk chk_dec
    lane is_lane_write lanes vdata 64 lane_index byte_addr
    h_Htot h_rftouch h_rffun s_lanes h_keep Hpb Hfrf s_rf_src s_rf_tgt s_ctx_silent s_chk_nonmem
    h_rwdisj s_lane_write_is_write s_one_write_per_lane s_footprint n_value n_po_hart n_po_total
    n_inst_hart n_window n_deps.
