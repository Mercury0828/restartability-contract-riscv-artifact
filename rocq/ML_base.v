(* ML_base.v — RESTART-V: the carrier and reads-from of the contracted execution when SEVERAL
   provisional lanes are erased at once.

   The frozen development fixes one duplicate pair (k, d). The vector specification lets every element
   past `vstart` have been written before the fault, so a fault run carries one pair per provisionally
   written lane. This file fixes the vocabulary for that general case:

     LS          the lanes, as a finite list of (keeper, deleted) pairs — keeper = first attempt,
                 deleted = replay;
     isdel       membership in the deleted set (decidable, from the list);
     carrier_L   the fault carrier with every deleted duplicate removed;
     survivor_L  its membership predicate;
     rf_L        reads-from with every read of a deleted duplicate retargeted to that lane's keeper.

   Nothing here is about memory models; the theorems live in ML_T1.v. No Admitted, no axioms.
   Coq 8.15. *)

Require Import Coq.Lists.List.
Import ListNotations.

Section MLBase.

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable E0 : list Event.
  Variable LS : list (Event * Event).    (* (keeper, deleted), one pair per provisional lane *)

  Definition dels : list Event := map snd LS.
  Definition isdel (x : Event) : Prop := In x dels.
  Definition isdel_dec (x : Event) : {isdel x} + {~ isdel x} := in_dec eq_ev_dec x dels.

  Definition carrier_L : list Event :=
    filter (fun e => if isdel_dec e then false else true) E0.

  Definition survivor_L (x : Event) : Prop := In x E0 /\ ~ isdel x.

  Lemma survivor_carrier : forall x, In x carrier_L <-> survivor_L x.
  Proof.
    intro x. unfold carrier_L, survivor_L. rewrite filter_In.
    destruct (isdel_dec x) as [D | N]; split.
    - intros [_ H]; discriminate H.
    - intros [_ H]; contradiction.
    - intros [H _]; split; [exact H | exact N].
    - intros [H _]; split; [exact H | reflexivity].
  Qed.

  Lemma carrier_sub : forall x, In x carrier_L -> In x E0.
  Proof. intros x H. apply survivor_carrier in H. destruct H as [H _]; exact H. Qed.

  Lemma isdel_lane : forall d, isdel d <-> exists k, In (k, d) LS.
  Proof.
    intro d. unfold isdel, dels. rewrite in_map_iff. split.
    - intros [[k d'] [E H]]. simpl in E. subst d'. exists k. exact H.
    - intros [k H]. exists (k, d). split; [reflexivity | exact H].
  Qed.

  Lemma lane_del : forall k d, In (k, d) LS -> isdel d.
  Proof. intros k d H. apply isdel_lane. exists k; exact H. Qed.

  Variable Byte : Type.

  (* A read of a deleted duplicate d is retargeted to d's keeper; any other source is kept. *)
  Definition rf_L (rf : Event -> Byte -> Event -> Prop) (w : Event) (b : Byte) (r : Event) : Prop :=
    (rf w b r /\ ~ (exists d, isdel d /\ rf d b r)) \/
    (exists d, In (w, d) LS /\ rf d b r).

End MLBase.

(* For one lane the general carrier is the frozen development's contracted carrier, definitionally up
   to the decision procedure used for "is this event deleted". *)
Lemma filter_pointwise :
  forall (A : Type) (f g : A -> bool) (l : list A),
    (forall x, f x = g x) -> filter f l = filter g l.
Proof.
  intros A f g l H. induction l as [| a t IH]; simpl; [reflexivity |].
  rewrite (H a). destruct (g a); rewrite IH; reflexivity.
Qed.
