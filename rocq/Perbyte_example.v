(* Perbyte_example.v — RESTART-V: the mixed-size run that separates the per-byte check from the
   union-graph check.

   Bytes x and y are adjacent, x halfword-aligned, both initially 0 (init writes Ix, Iy).
       hart 0:  Wx: sb x=1 ;  R0: lh (x,y)  reads (1,0)
       hart 1:  Wy: sb y=1 ;  R1: lh (x,y)  reads (0,1)
   Global memory order: Ix < Iy < R0 < R1 < Wx < Wy. Each load takes one byte from its own earlier
   store and the other byte from initial memory.

   Proved here:
     * the run satisfies the load-value rule over that order (`ex_load_value`) and rules r1 and r2
       of preserved program order have no instance in it, so it is an RVWMO execution;
     * hence, by `Perbyte.rvwmo_perbyte_coherence`, it passes the per-byte check at both bytes
       (`ex_perbyte_ok`);
     * the union graph `Clift_coherence.Cf` has the cycle
           Wx -rf_x-> R0 -fr_y-> Wy -rf_y-> R1 -fr_x-> Wx          (`ex_union_cycle`).

   0 Admitted / 0 axioms. Modifies no existing .v file. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.micromega.Lia.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Perbyte.
Import ListNotations.

Inductive Ev := Ix | Iy | Wx | Wy | R0 | R1.
Inductive By := X | Y.

Definition ev_eq_dec : forall a b : Ev, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition E : list Ev := [Ix; Iy; Wx; Wy; R0; R1].

Definition is_write (e : Ev) : Prop :=
  match e with Ix | Iy | Wx | Wy => True | _ => False end.
Definition is_read (e : Ev) : Prop :=
  match e with R0 | R1 => True | _ => False end.

Definition touches (e : Ev) (b : By) : Prop :=
  match e, b with
  | Ix, X | Wx, X => True
  | Iy, Y | Wy, Y => True
  | R0, _ | R1, _ => True
  | _, _ => False
  end.

Definition wval (e : Ev) (_ : By) : nat := match e with Wx | Wy => 1 | _ => 0 end.

Definition rank (e : Ev) : nat :=
  match e with Ix => 0 | Iy => 1 | R0 => 2 | R1 => 3 | Wx => 4 | Wy => 5 end.
Definition gmo (a b : Ev) : Prop := rank a < rank b.

Definition po (a b : Ev) : Prop :=
  (a = Wx /\ b = R0) \/ (a = Wy /\ b = R1).
Definition poloc (a b : Ev) : Prop := po a b /\ exists bb, touches a bb /\ touches b bb.

Definition rf (w : Ev) (b : By) (r : Ev) : Prop :=
  (w = Wx /\ b = X /\ r = R0) \/ (w = Iy /\ b = Y /\ r = R0) \/
  (w = Ix /\ b = X /\ r = R1) \/ (w = Wy /\ b = Y /\ r = R1).

(* the values the two loads return: (1,0) and (0,1) *)
Lemma ex_values :
  (forall w, rf w X R0 -> wval w X = 1) /\ (forall w, rf w Y R0 -> wval w Y = 0) /\
  (forall w, rf w X R1 -> wval w X = 0) /\ (forall w, rf w Y R1 -> wval w Y = 1).
Proof.
  unfold rf; repeat split; intros w H;
    repeat match goal with
           | H : _ \/ _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           end; subst; try discriminate; reflexivity.
Qed.

Ltac allE := unfold E; simpl; tauto.
Ltac pick_rf := try unfold rf;
  first [ left; repeat split; reflexivity
        | right; first [ left; repeat split; reflexivity
                       | right; first [ left; repeat split; reflexivity
                                      | right; repeat split; reflexivity ] ] ].

Lemma ex_irr : forall e, In e E -> ~ gmo e e.
Proof. intros e _. unfold gmo. lia. Qed.
Lemma ex_tr : forall a b c, In a E -> In b E -> In c E -> gmo a b -> gmo b c -> gmo a c.
Proof. intros a b c _ _ _. unfold gmo. lia. Qed.
Lemma ex_tot : forall a b, In a E -> In b E -> a <> b -> gmo a b \/ gmo b a.
Proof. intros a b _ _ H. unfold gmo. destruct a, b; simpl; try lia; exfalso; apply H; reflexivity. Qed.

Lemma ex_po_irr : forall e, ~ po e e.
Proof. intros e [[H1 H2] | [H1 H2]]; subst; discriminate. Qed.
Lemma ex_po_tr : forall a b c, po a b -> po b c -> po a c.
Proof.
  intros a b c [[_ H1] | [_ H1]] [[H2 _] | [H2 _]]; subst; discriminate.
Qed.

Lemma ex_rw : forall e, is_read e -> is_write e -> False.
Proof. intros e; destruct e; simpl; tauto. Qed.
Lemma ex_mem : forall e b, In e E -> touches e b -> is_read e \/ is_write e.
Proof. intros e b _ _. destruct e; simpl; tauto. Qed.
Lemma ex_poloc : forall x y, poloc x y -> po x y /\ In x E /\ In y E.
Proof. intros x y [Hp _]. split; [exact Hp |]. destruct x, y; split; allE. Qed.

Lemma ex_rf_tgt : forall w b r, rf w b r -> is_read r /\ In r E.
Proof.
  intros w b r H. unfold rf in H.
  repeat match goal with H : _ \/ _ |- _ => destruct H | H : _ /\ _ |- _ => destruct H end;
    subst; simpl; split; auto; allE.
Qed.

Lemma ex_rf_fun : forall w1 w2 b r, rf w1 b r -> rf w2 b r -> w1 = w2.
Proof.
  intros w1 w2 b r H1 H2. unfold rf in *.
  repeat match goal with H : _ \/ _ |- _ => destruct H | H : _ /\ _ |- _ => destruct H end;
    subst; try discriminate; reflexivity.
Qed.

Lemma ex_rf_total : forall r b, In r E -> is_read r -> touches r b -> exists w, rf w b r.
Proof.
  intros r b _ Hr _. unfold rf. destruct r; try contradiction; destruct b.
  - exists Wx; pick_rf.
  - exists Iy; pick_rf.
  - exists Ix; pick_rf.
  - exists Wy; pick_rf.
Qed.

(* the load-value rule over gmo: each source is the gmo-latest write of the byte that precedes the
   load in gmo or in program order *)
Lemma ex_load_value : forall b r w, is_read r -> In r E -> rf w b r ->
    L1_abstract_erasure.C4_source Ev By is_write touches gmo po E b r w.
Proof.
  intros b r w _ _ H. unfold rf in H.
  unfold L1_abstract_erasure.C4_source, L1_abstract_erasure.cand.
  repeat match goal with H : _ \/ _ |- _ => destruct H | H : _ /\ _ |- _ => destruct H end; subst;
  (split; [ repeat split; simpl; auto; try allE; unfold gmo, po; simpl;
            first [ left; lia | right; auto | auto ] |]);
  intros w' [Iw' [Ww' [Tw' O]]]; unfold gmo, po in *;
  destruct w'; simpl in *; try contradiction; try (left; reflexivity); try (right; lia);
  destruct O as [O | [[O1 O2] | [O1 O2]]]; try lia; try discriminate.
Qed.

(* rules r1 and r2 have no instance: no store follows any access in program order, and no two
   loads are program-ordered *)
Lemma ex_r1 : forall x y b, In x E -> In y E -> po x y -> touches x b -> touches y b ->
    is_write y -> gmo x y.
Proof. intros x y b _ _ [[_ H] | [_ H]] _ _ Wy; subst; contradiction. Qed.

Lemma ex_r2 : forall x y b, In x E -> In y E -> is_read x -> is_read y ->
    touches x b -> touches y b -> po x y ->
    ~ (exists w, In w E /\ is_write w /\ touches w b /\ po x w /\ po w y) ->
    ~ (exists w, rf w b x /\ rf w b y) -> gmo x y.
Proof. intros x y b _ _ Rx _ _ _ [[H _] | [H _]]; subst; contradiction. Qed.

(* the run passes the per-byte check at every byte *)
Theorem ex_perbyte_ok :
  forall b x, ~ clos_trans Ev (CfB Ev By gmo is_write is_read touches E rf poloc b) x x.
Proof.
  intro b.
  exact (rvwmo_perbyte_coherence Ev By ev_eq_dec gmo is_write is_read touches E rf po poloc
           ex_irr ex_tr ex_tot ex_po_irr ex_po_tr ex_rw ex_mem ex_poloc ex_load_value ex_rf_tgt
           ex_rf_fun ex_rf_total ex_r1 ex_r2 b).
Qed.

(* ... and fails the union-graph check *)
Theorem ex_union_cycle :
  clos_trans Ev (Clift_coherence.Cf Ev By gmo is_write is_read touches E rf poloc) Wx Wx.
Proof.
  assert (Hrf : forall w b r, rf w b r ->
            Clift_coherence.Cf Ev By gmo is_write is_read touches E rf poloc w r)
    by (intros w b r H; right; right; left; exists b; exact H).
  assert (Hfr : forall r w1 w2 b, is_read r -> rf w1 b r -> In w1 E -> In w2 E ->
            is_write w1 -> is_write w2 -> touches w1 b -> touches w2 b -> gmo w1 w2 ->
            Clift_coherence.Cf Ev By gmo is_write is_read touches E rf poloc r w2).
  { intros r w1 w2 b Rr H I1 I2 W1 W2 T1 T2 G. right; left. exists b. split; [exact Rr |].
    exists w1. split; [exact H |]. unfold Clift_coherence.co_flt, Clift_coherence.coOn,
    Clift_coherence.inE0. repeat split; assumption. }
  apply (t_trans _ _ Wx R0 Wx).
  { apply t_step. apply (Hrf Wx X R0). pick_rf. }
  apply (t_trans _ _ R0 Wy Wx).
  { apply t_step. apply (Hfr R0 Iy Wy Y); simpl; auto; try allE.
    - pick_rf.
    - unfold gmo; simpl; lia. }
  apply (t_trans _ _ Wy R1 Wx).
  { apply t_step. apply (Hrf Wy Y R1). pick_rf. }
  apply t_step. apply (Hfr R1 Ix Wx X); simpl; auto; try allE.
  - pick_rf.
  - unfold gmo; simpl; lia.
Qed.
