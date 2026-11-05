(* Alpha_regs_instance.v — alpha_regs is satisfiable, and it is not vacuous either way.
 *
 * Alpha_regs.v derives the duplicate pair's value equality from alpha_regs. That derivation is worth
 * nothing if alpha_regs cannot hold, and it says nothing if alpha_regs holds of every handler. Both
 * are checked here:
 *
 *   POSITIVE  a repair handler that writes the protection entry and returns satisfies alpha_regs,
 *             and the duplicate pair it yields is exhibited with a computed byte footprint;
 *   NEGATIVE  a handler that clobbers the data vector register does NOT satisfy it, so the property
 *             discriminates. Without this the derivation would be true but empty.
 *
 * The state is the store's inputs plus the two things the trap really does change -- the protection
 * entry and vstart -- so the positive handler is exactly the shape of the one in the paper: it widens
 * the protection entry and leaves everything the store reads alone.
 *
 * No Admitted, no axioms. Coq 8.15.
 *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import RestartV.Multi_lane.
Require Import RestartV.Alpha_regs.

(* ------------------------------------------------------------------------ the concrete state *)

Record St : Type := mkSt {
  s_base   : nat;          (* rs1, the base address register *)
  s_data   : nat -> nat;   (* vs3, the data vector register, element-indexed *)
  s_vl     : nat;
  s_eew    : nat;
  s_mask   : nat -> bool;
  s_pmp    : nat;          (* the protection entry the handler repairs *)
  s_vstart : nat           (* set by the trap, deliberately NOT an input of the lane writes *)
}.

(* unit-stride addressing, real byte extraction, and a byte-interval footprint *)
Definition LADDR (base eew i : nat) : nat := base + eew * i.
Definition LBYTES (v b : nat) : nat := (v / (Nat.pow 256 b)) mod 256.
Definition FOOT (a w b : nat) : Prop := a <= b /\ b < a + w.

(* ------------------------------------------------------------------------------- handlers *)

(* The repair handler: widen the protection entry, take the trap's vstart, touch nothing else. *)
Definition Hrepair (s : St) : St :=
  mkSt (s_base s) (s_data s) (s_vl s) (s_eew s) (s_mask s) 1 (s_vstart s + 1).

(* A handler that does not preserve the store's inputs: it zeroes the data register. *)
Definition Hclobber (s : St) : St :=
  mkSt (s_base s) (fun _ => 0) (s_vl s) (s_eew s) (s_mask s) 1 (s_vstart s + 1).

Definition S0 : St := mkSt 1000 (fun i => 7 + i) 4 8 (fun _ => true) 0 0.

(* --------------------------------------------------------------------- POSITIVE: it holds *)

Theorem ar_i_alpha :
  forall s, alpha_regs St nat nat s_base s_data s_vl s_eew s_mask Hrepair s.
Proof.
  intro s. unfold alpha_regs, Hrepair. simpl.
  split; [reflexivity |].
  split; [intro i; reflexivity |].
  split; [reflexivity |].
  split; [reflexivity | intro i; reflexivity].
Qed.

(* --------------------------------------------------------- NEGATIVE: it is not automatic *)

Theorem ar_i_alpha_fails_when_data_clobbered :
  ~ alpha_regs St nat nat s_base s_data s_vl s_eew s_mask Hclobber S0.
Proof.
  intros [_ [Hd _]]. specialize (Hd 0). unfold Hclobber, S0 in Hd. simpl in Hd. discriminate.
Qed.

(* -------------------------------------------------- the derived duplicate pair, instantiated *)

Definition TCHi (s : St) (i : nat) : Ev -> nat -> Prop :=
  ev_touches St nat nat s_base s_eew LADDR FOOT Hrepair s i.

Definition WVi (s : St) (i : nat) : Ev -> nat -> nat :=
  ev_wval St nat nat s_data LBYTES Hrepair s i.

(* The value-equality antecedent of the erasure theorems, now discharged for a real handler. *)
Theorem ar_i_dup :
  forall s i, Dup Ev nat nat ev_is_write (TCHi s i) (WVi s i) false true.
Proof.
  intros s i. unfold TCHi, WVi.
  apply (alpha_regs_gives_Dup St nat nat nat s_base s_data s_vl s_eew s_mask
           LADDR LBYTES FOOT Hrepair s i).
  apply ar_i_alpha.
Qed.

(* And the two lane conditions the multi-lane fold consumes. *)
Theorem ar_i_lane_conditions :
  forall s i,
    (forall b, TCHi s i true b -> TCHi s i false b)
    /\ (forall b, TCHi s i true b -> WVi s i false b = WVi s i true b).
Proof.
  intros s i. unfold TCHi, WVi.
  apply (alpha_regs_gives_lane_conditions St nat nat nat s_base s_data s_vl s_eew s_mask
           LADDR LBYTES FOOT Hrepair s i).
  apply ar_i_alpha.
Qed.

(* The footprint is a computed byte interval, not an abstract predicate: lane 3 of a `vse64.v` based
   at 1000 covers bytes 1024..1031, before the trap and after it alike. *)
Theorem ar_i_footprint_lane3 :
  forall b, TCHi S0 3 false b <-> (1024 <= b /\ b < 1032).
Proof.
  intro b. unfold TCHi, ev_touches, ev_state, lfoot, la, LADDR, FOOT, S0. simpl. tauto.
Qed.

Theorem ar_i_footprint_lane3_replay :
  forall b, TCHi S0 3 true b <-> (1024 <= b /\ b < 1032).
Proof.
  intro b. unfold TCHi, ev_touches, ev_state, lfoot, la, LADDR, FOOT, Hrepair, S0. simpl. tauto.
Qed.

(* The byte the replay writes at offset 0 of lane 3 is the byte the first attempt wrote there. *)
Theorem ar_i_value_lane3 :
  WVi S0 3 true 0 = WVi S0 3 false 0 /\ WVi S0 3 false 0 = 10.
Proof.
  unfold WVi, ev_wval, ev_state, lv, LBYTES, Hrepair, S0. simpl.
  split; reflexivity.
Qed.
