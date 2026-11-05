(* Frozen_mainmodel.v — RESTART-V M4: wire the concrete frozen PPO into Rlift, DISCHARGING the
   `ppo_lifts` premise of the main-model witness acyclicity.

   Rlift_mainmodel.`witness_mainmodel_acyclic` took `ppo_lifts` as an abstract premise. PPO_union
   proves it for the frozen fragment (`ppo_wit_lifts`). This file instantiates Rlift's abstract fault
   `ppo` with the frozen fault PPO (ppoF ∪ fault-r2), injects both into the main-model union Rf, and
   supplies `ppo_wit_lifts` — obtaining `frozen_witness_mainmodel_acyclic` with NO `ppo_lifts`
   premise: the witness main-model relation is acyclic whenever the fault run's is, for the frozen
   fragment, modulo the explicit RO/token adapter hypotheses (po-twin etc.).

   Self-contained modulo Rlift + PPO_union; 0 Admitted / 0 axioms (Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import RestartV.Rlift_mainmodel.
Require Import RestartV.PPO_union.
Import ListNotations.

Section FrozenMain.

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte Hart : Type.
  Variable gmo : Event -> Event -> Prop.
  Variable is_write is_read is_load is_store : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable same_addr addr data ctrl fence : Event -> Event -> Prop.
  Variable hart : Event -> Hart.
  Variable E0 : list Event.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable po : Event -> Event -> Prop.
  Variables d k : Event.

  (* frozen fault PPO = the syntactic/r13/r12 union ∪ the (byte-indexed) fault r2 edges *)
  Definition fault_ppo (x y : Event) : Prop :=
    PPO_union.ppoF Event Byte po is_load is_store same_addr addr data ctrl fence rf x y \/
    (exists bx, PPO_union.r2F Event Byte po is_read is_write touches rf E0 bx x y).

  Definition FRf :=
    Rlift_mainmodel.Rf Event Byte Hart gmo is_write is_read touches hart E0 rf fault_ppo.

  Lemma ppoF_inj :
    forall x y,
      PPO_union.ppoF Event Byte po is_load is_store same_addr addr data ctrl fence rf x y -> FRf x y.
  Proof. intros x y H. unfold FRf, Rlift_mainmodel.Rf. right. right. right. left. exact H. Qed.

  Lemma r2F_inj :
    forall x a b,
      PPO_union.r2F Event Byte po is_read is_write touches rf E0 x a b -> FRf a b.
  Proof. intros x a b H. unfold FRf, Rlift_mainmodel.Rf. right. right. right. right. exists x. exact H. Qed.

  Hypothesis d_in : In d E0.
  Hypothesis d_w  : is_write d.
  Hypothesis k_in : In k E0.
  Hypothesis k_w  : is_write k.
  Hypothesis kd_ne : k <> d.
  Hypothesis rf_touches : forall w bb r, rf w bb r -> touches w bb.
  Hypothesis keeper_before : gmo k d.
  Hypothesis hart_dk : hart d = hart k.
  Hypothesis Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.
  Hypothesis Hadj : forall b, touches d b ->
      Rlift_mainmodel.adj Event Byte gmo is_write touches E0 d k b.
  Hypothesis foot_dk : forall x, touches d x -> touches k x.
  Hypothesis po_twin : forall a b x,
    is_read a -> touches a x -> touches d x -> po a d -> po d b -> po a k /\ po k b.
  Hypothesis rf_functional : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.
  Hypothesis dup_r12 : forall a b bb,
      po a k -> po k b -> (addr a k \/ data a k) -> rf d bb b ->
      po a d /\ po d b /\ (addr a d \/ data a d).

  Definition frozen_ppo_wit :=
    PPO_union.ppo_wit Event Byte po is_load is_store is_read is_write
      same_addr addr data ctrl fence touches rf E0 d k.

  Lemma frozen_ppo_lifts : forall x y, frozen_ppo_wit x y -> clos_trans Event FRf x y.
  Proof.
    apply (PPO_union.ppo_wit_lifts Event eq_ev_dec Byte po is_load is_store is_read is_write
             same_addr addr data ctrl fence touches rf E0 FRf d k
             ppoF_inj k_in k_w kd_ne foot_dk po_twin rf_functional dup_r12 r2F_inj).
  Qed.

  (* Main-model witness acyclicity for the frozen fragment, ppo_lifts DISCHARGED. *)
  Theorem frozen_witness_mainmodel_acyclic :
    (forall x, ~ clos_trans Event FRf x x) ->
    forall x, ~ clos_trans Event
      (Rlift_mainmodel.Rn Event Byte Hart gmo is_write is_read touches hart E0 rf frozen_ppo_wit d k)
      x x.
  Proof.
    intro Hacyc.
    exact (Rlift_mainmodel.witness_mainmodel_acyclic Event Byte Hart gmo is_write is_read touches
             hart E0 rf fault_ppo frozen_ppo_wit d k
             d_in d_w k_in k_w rf_touches keeper_before hart_dk
             (Rlift_mainmodel.Build_gmo_wf Event gmo E0 Htot) Hadj
             frozen_ppo_lifts Hacyc).
  Qed.

End FrozenMain.
