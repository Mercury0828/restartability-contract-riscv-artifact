(* Alpha_regs.v — the duplicate pair's value equality, discharged from a handler property.
 *
 * L1 and Multi_lane both take "the first attempt and the replay have the same byte footprint and the
 * same byte values" as an ANTECEDENT. That is the honest reading of alpha as stated in the contract:
 * alpha constrains what the handler does to protection state and to memory, not what it does to the
 * registers the store's address and data come from. This file closes that gap.
 *
 * The content is not the final rewrite -- it is making explicit exactly WHICH architectural state a
 * unit-stride vector store's lane writes are a function of, and then showing that a handler which
 * leaves that state alone forces the two attempts to coincide. Two things follow:
 *
 *   1. the lane's address, byte footprint and byte values are equal across the trap;
 *   2. the first attempt and the replay form a Dup pair in the sense Multi_lane.v requires,
 *      so the value-equality antecedent is DERIVED rather than assumed.
 *
 * What this does NOT do: it does not prove the concrete handler satisfies alpha_regs. That is an
 * instruction-level obligation about the handler image, discharged separately.
 *
 * No Admitted, no axioms. Coq 8.15.
 *)

From Coq Require Import List Arith Bool.
Import ListNotations.
Require Import RestartV.Multi_lane.

Section AlphaRegs.

  Variable State : Type.
  Variable Addr  : Type.
  Variable Byte  : Type.
  Variable Value : Type.

  (* ---------------------------------------------------------- the store's architectural inputs *)

  (* Exactly the state a unit-stride vector store's lane writes read: the base address register, the
     data vector register, vl, the element width from vtype, and the mask. vstart is deliberately NOT
     among them -- the replay starts at a different vstart, and that is the whole point. *)
  Variable get_base : State -> Addr.
  Variable get_data : State -> nat -> Value.
  Variable get_vl   : State -> nat.
  Variable get_eew  : State -> nat.
  Variable get_mask : State -> nat -> bool.

  (* The unit-stride addressing and byte decomposition. Both are pure functions of the inputs above:
     address of lane i is derived from base and eew, and the bytes of a lane are the bytes of the
     element the data register holds at that index. *)
  Variable lane_addr : Addr -> nat -> nat -> Addr.        (* base -> eew -> index -> address *)
  Variable lane_bytes : Value -> Byte -> Value.           (* element -> byte offset -> byte value *)
  Variable footprint : Addr -> nat -> Byte -> Prop.       (* address -> width -> byte *)

  Definition la (s : State) (i : nat) : Addr := lane_addr (get_base s) (get_eew s) i.
  Definition lv (s : State) (i : nat) (b : Byte) : Value := lane_bytes (get_data s i) b.
  Definition lfoot (s : State) (i : nat) (b : Byte) : Prop := footprint (la s i) (get_eew s) b.
  Definition lact (s : State) (i : nat) : bool := get_mask s i && (i <? get_vl s).

  (* ------------------------------------------------------------------- the handler property *)

  Variable H : State -> State.

  (* alpha_regs: the handler image agrees with the pre-trap state on every input the store reads.
     Stated componentwise rather than as one record equality, so no functional extensionality is
     needed anywhere below. *)
  Definition alpha_regs (s : State) : Prop :=
    get_base (H s) = get_base s
    /\ (forall i, get_data (H s) i = get_data s i)
    /\ get_vl (H s) = get_vl s
    /\ get_eew (H s) = get_eew s
    /\ (forall i, get_mask (H s) i = get_mask s i).

  (* ------------------------------------------------- the replay reproduces the first attempt *)

  Theorem replay_lane_address :
    forall s i, alpha_regs s -> la (H s) i = la s i.
  Proof.
    intros s i [Hb [_ [_ [He _]]]]. unfold la. rewrite Hb, He. reflexivity.
  Qed.

  Theorem replay_lane_footprint :
    forall s i b, alpha_regs s -> (lfoot (H s) i b <-> lfoot s i b).
  Proof.
    intros s i b Ha. unfold lfoot.
    rewrite (replay_lane_address s i Ha).
    destruct Ha as [_ [_ [_ [He _]]]]. rewrite He. reflexivity.
  Qed.

  Theorem replay_lane_value :
    forall s i b, alpha_regs s -> lv (H s) i b = lv s i b.
  Proof.
    intros s i b [_ [Hd _]]. unfold lv. rewrite Hd. reflexivity.
  Qed.

  (* The same lanes are active, so the replay writes neither more nor fewer of them. *)
  Theorem replay_lane_active :
    forall s i, alpha_regs s -> lact (H s) i = lact s i.
  Proof.
    intros s i [_ [_ [Hv [_ Hm]]]]. unfold lact. rewrite Hv, Hm. reflexivity.
  Qed.

  (* ------------------------------------------------------- the duplicate pair, now derived *)

  (* Two events: the first attempt at lane i, and the replay of lane i. *)
  Definition Ev := bool.
  Definition ev_state (s : State) (e : Ev) : State := if e then H s else s.

  Definition ev_is_write (_ : Ev) : Prop := True.
  Definition ev_touches (s : State) (i : nat) (e : Ev) (b : Byte) : Prop := lfoot (ev_state s e) i b.
  Definition ev_wval (s : State) (i : nat) (e : Ev) (b : Byte) : Value := lv (ev_state s e) i b.

  (* This is the statement the erasure theorems took as an antecedent. Under alpha_regs it is a
     consequence: a handler that does not disturb the store's inputs cannot make the replay write
     anything other than what the first attempt wrote. *)
  Theorem alpha_regs_gives_Dup :
    forall s i, alpha_regs s ->
      Dup Ev Byte Value ev_is_write (ev_touches s i) (ev_wval s i) false true.
  Proof.
    intros s i Ha. constructor.
    - exact I.
    - exact I.
    - intro b. unfold ev_touches, ev_state. simpl.
      symmetry. apply replay_lane_footprint. exact Ha.
    - intros b _. unfold ev_wval, ev_state. simpl.
      symmetry. apply replay_lane_value. exact Ha.
  Qed.

  (* Composed with Multi_lane's orientation lemma: the keeper is the first attempt, the erased event
     is the replay, and the two lane conditions the fold needs are now both discharged from alpha. *)
  Theorem alpha_regs_gives_lane_conditions :
    forall s i, alpha_regs s ->
      (forall b, ev_touches s i true b -> ev_touches s i false b)
      /\ (forall b, ev_touches s i true b -> ev_wval s i false b = ev_wval s i true b).
  Proof.
    intros s i Ha.
    apply (dup_gives_agreement Ev Byte Value ev_is_write (ev_touches s i) (ev_wval s i)
             false true false true).
    - apply alpha_regs_gives_Dup. exact Ha.
    - right. split; reflexivity.
  Qed.

End AlphaRegs.
