(* ML_instance_stage2.v — RESTART-V: the two-lane run of ML_instance.v inhabits EVERY premise of the
   general-lane Stage-2 capstone `ML_stage2.ML_stage2_endtoend`, which is then applied to it.

   Same run as ML_instance.v (VL = 4, K = 1, P = {2, 3}, natural interleaving). The Stage-2 data:
     trap region   Ctx = {Tr, Xr}                     (memory-silent)
     check events  none in this slice
     lanes         0..3, lane writes W0, F1, K2/D2, K3/D3
     PMP geometry  dst = 64, lane i at [64 + 8i, 72 + 8i), background RAM [0, 1000), fault lane 1

   After both replays and the trap region are erased, the kernel holds exactly one write per lane
   (W0, F1, K2, K3), which is Layer 3's one-write-per-lane premise.

   0 Admitted / 0 axioms. Modifies no existing .v file. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.micromega.Lia.
Require Import RestartV.Ctx_erasure.
Require Import RestartV.Frozen_pmp.
Require Import RestartV.ML_base.
Require Import RestartV.ML_T1.
Require Import RestartV.ML_stage2.
Require Import RestartV.ML_instance.
Import ListNotations.

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
  ML_T1.LaneOK Ev Lb unit nat gmo is_write is_read touches wval addr data hart E0 rf po k d.
Proof.
  intros k d H.
  exact (ML_T1.LaneTok_LaneOK Ev Lb unit nat gmo is_write is_read touches wval addr data hart E0 rf
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

(* ---------------------------------------------------------------- apply the capstone *)

Definition ml_stage2_instance :=
  ML_stage2.ML_stage2_endtoend
    Ev ev_eq_dec Lb unit nat Ln gmo is_write is_read is_read is_write touches wval
    same_addr addr data ctrl fence hart E0 rf po poloc LS Ctx ctx_dec is_chk chk_dec
    lane is_lane_write lanes
    h_Hirr h_Htr h_Htot h_potrans h_rfC4 h_rftouch h_rffun s_lanes h_keep Hcf Hfrf
    s_rf_src s_rf_tgt s_poloc s_ctx_silent s_chk_nonmem
    64 4 1 0 1000 lane_index byte_addr
    s_K_lt s_bg s_nonempty s_complete s_in_range s_cover s_inj s_footprint
    s_one_write_per_lane s_lane_write_is_write.
