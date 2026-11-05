(* Gamma_adj_obs.v — RESTART-V: without gamma_adj, NO single-write execution reproduces what the
   faulting run lets another hart read.

   `Gamma_adj_needed.v` shows that erasing the replay with the keeper's coherence position changes
   the final memory when a foreign write lies coherence-between keeper and replay. That leaves open
   whether some OTHER fault-free execution could still match the run. This file closes that question
   with a reader:

       hart 0 (faulting):  K: lane write x=1          ...trap, repair...   D: replay x=1
       hart 2:             W: x=2
       hart 1 (reader):    Q1: x -> 1 ;  Q2: x -> 2 ;  Q3: x -> 1
       coherence  Ini < K < W < D,  global memory order  Ini K Q1 W Q2 D Q3.

   (1) `fault_run_*`: the run satisfies the load-value rule, passes the per-byte check and the
       main-model check, and its lane pair (K,D) meets every lane premise of Theorem 1 except
       gamma_adj, which fails (`fault_run_not_adj`).
   (2) `single_write_no_121`: in ANY candidate execution in which value 1 is written to x by a single
       write and value 2 by a single write, three program-ordered reads of x that return 1, 2, 1 close
       a cycle of the per-byte check. A fault-free run of the program writes x=1 once (the lane) and
       x=2 once, so none of its consistent executions returns 1, 2, 1.

   0 Admitted / 0 axioms. Modifies no existing .v file. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.micromega.Lia.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Rlift_mainmodel.
Require Import RestartV.PPO_union.
Require Import RestartV.Frozen_mainmodel.
Require Import RestartV.Perbyte.
Import ListNotations.

(* ==================================================================================================
   (2) the generic impossibility
   ================================================================================================== *)

Section SingleWrite.

  Variable Event Byte Value : Type.
  Variable gmo : Event -> Event -> Prop.
  Variable is_write is_read : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable E : list Event.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable poloc : Event -> Event -> Prop.
  Variable wval : Event -> Byte -> Value.
  Variable x : Byte.
  Variables k w q1 q2 q3 : Event.
  Variables v1 v2 : Value.

  Hypothesis Hk : In k E /\ is_write k /\ touches k x.
  Hypothesis Hw : In w E /\ is_write w /\ touches w x.
  Hypothesis Hkw : k <> w.
  Hypothesis Htot : forall a b, In a E -> In b E -> a <> b -> gmo a b \/ gmo b a.
  (* value 1 is written to x by k alone, value 2 by w alone *)
  Hypothesis Honly1 : forall e, In e E -> is_write e -> touches e x -> wval e x = v1 -> e = k.
  Hypothesis Honly2 : forall e, In e E -> is_write e -> touches e x -> wval e x = v2 -> e = w.
  Hypothesis Hsrc : forall e r, rf e x r -> In e E /\ is_write e /\ touches e x.
  Hypothesis Hq : is_read q1 /\ is_read q2 /\ is_read q3 /\
                  touches q1 x /\ touches q2 x /\ touches q3 x.
  Hypothesis Hpo : poloc q1 q2 /\ poloc q2 q3.

  Definition PBx := CfB Event Byte gmo is_write is_read touches E rf poloc x.

  Lemma PBx_rf : forall s r, rf s x r -> PBx s r.
  Proof. intros s r H. right; right; left. exists x. split; [reflexivity | exact H]. Qed.

  Lemma PBx_fr : forall r s s', is_read r -> rf s x r -> In s E -> In s' E -> is_write s ->
      is_write s' -> touches s x -> touches s' x -> gmo s s' -> PBx r s'.
  Proof.
    intros r s s' Rr H I1 I2 W1 W2 T1 T2 G. right; left. exists x. split; [exact Rr |].
    exists s. split; [split; [reflexivity | exact H] |].
    unfold Clift_coherence.co_flt, Clift_coherence.coOn, Clift_coherence.inE0, touches_at.
    repeat split; assumption.
  Qed.

  Lemma PBx_poloc : forall a b, poloc a b -> touches a x -> touches b x -> PBx a b.
  Proof. intros a b H Ta Tb. right; right; right. split; [exact H | split; assumption]. Qed.

  Theorem single_write_no_121 :
    (exists s1, rf s1 x q1 /\ wval s1 x = v1) ->
    (exists s2, rf s2 x q2 /\ wval s2 x = v2) ->
    (exists s3, rf s3 x q3 /\ wval s3 x = v1) ->
    exists e, clos_trans Event PBx e e.
  Proof.
    intros [s1 [H1 V1]] [s2 [H2 V2]] [s3 [H3 V3]].
    destruct Hk as [Ik [Wk Tk]]. destruct Hw as [Iw [Ww Tw]].
    destruct Hq as [R1 [R2 [R3 [T1 [T2 T3]]]]]. destruct Hpo as [P12 P23].
    destruct (Hsrc s1 q1 H1) as [I1 [W1 Ts1]].
    destruct (Hsrc s2 q2 H2) as [I2 [W2 Ts2]].
    destruct (Hsrc s3 q3 H3) as [I3 [W3 Ts3]].
    pose proof (Honly1 s1 I1 W1 Ts1 V1) as E1. pose proof (Honly2 s2 I2 W2 Ts2 V2) as E2.
    pose proof (Honly1 s3 I3 W3 Ts3 V3) as E3. subst s1 s2 s3.
    destruct (Htot k w Ik Iw Hkw) as [G | G].
    - (* k before w: Q2 -po-> Q3 -fr-> W -rf-> Q2 *)
      exists q2. apply (t_trans _ _ q2 q3 q2).
      { apply t_step. exact (PBx_poloc q2 q3 P23 T2 T3). }
      apply (t_trans _ _ q3 w q2).
      { apply t_step. exact (PBx_fr q3 k w R3 H3 Ik Iw Wk Ww Tk Tw G). }
      apply t_step. exact (PBx_rf w q2 H2).
    - (* w before k: Q1 -po-> Q2 -fr-> K -rf-> Q1 *)
      exists q1. apply (t_trans _ _ q1 q2 q1).
      { apply t_step. exact (PBx_poloc q1 q2 P12 T1 T2). }
      apply (t_trans _ _ q2 k q1).
      { apply t_step. exact (PBx_fr q2 w k R2 H2 Iw Ik Ww Wk Tw Tk G). }
      apply t_step. exact (PBx_rf k q1 H1).
  Qed.

End SingleWrite.

(* ==================================================================================================
   (1) the faulting run
   ================================================================================================== *)

Inductive Ev := Ini | K | W | D | Q1 | Q2 | Q3.

Definition ev_eq_dec : forall a b : Ev, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition E0 : list Ev := [Ini; K; W; D; Q1; Q2; Q3].

Definition rank (e : Ev) : nat :=
  match e with Ini => 0 | K => 1 | Q1 => 2 | W => 3 | Q2 => 4 | D => 5 | Q3 => 6 end.
Definition gmo (a b : Ev) : Prop := rank a < rank b.

Definition is_write (e : Ev) : Prop := match e with Ini | K | W | D => True | _ => False end.
Definition is_read (e : Ev) : Prop := match e with Q1 | Q2 | Q3 => True | _ => False end.
Definition touches (_ : Ev) (_ : unit) : Prop := True.
Definition wval (e : Ev) (_ : unit) : nat := match e with K | D => 1 | W => 2 | _ => 0 end.
Definition hart (e : Ev) : nat := match e with K | D => 0 | Q1 | Q2 | Q3 => 1 | W => 2 | Ini => 3 end.

Definition po (a b : Ev) : Prop :=
  match a, b with K, D | Q1, Q2 | Q2, Q3 | Q1, Q3 => True | _, _ => False end.
Definition poloc (a b : Ev) : Prop := po a b.
Definition same_addr (_ _ : Ev) : Prop := True.
Definition nodep (_ _ : Ev) : Prop := False.

Definition rf (s : Ev) (_ : unit) (r : Ev) : Prop :=
  (s = K /\ r = Q1) \/ (s = W /\ r = Q2) \/ (s = D /\ r = Q3).

Lemma po_rank : forall a b, po a b -> rank a < rank b.
Proof. intros a b H; destruct a, b; simpl in *; try contradiction; lia. Qed.

Lemma rf_cases : forall s u r, rf s u r -> (s = K /\ r = Q1) \/ (s = W /\ r = Q2) \/ (s = D /\ r = Q3).
Proof. intros s u r H; exact H. Qed.

(* every edge of either check climbs the rank, so both are acyclic *)
Lemma rank_acyclic : forall R : Ev -> Ev -> Prop,
    (forall a b, R a b -> rank a < rank b) -> forall e, ~ clos_trans Ev R e e.
Proof.
  intros R HR e H.
  assert (Hlt : forall a b, clos_trans Ev R a b -> rank a < rank b).
  { intros a b Hab. induction Hab as [a b Hab | a b c _ IH1 _ IH2]; [exact (HR a b Hab) | lia]. }
  pose proof (Hlt e e H). lia.
Qed.

(* reading a write and being fr-before a later write climbs the rank in this run *)
Lemma fr_rank : forall r s s', rf s tt r -> gmo s s' -> is_write s' -> rank r < rank s'.
Proof.
  intros r s s' H G Ws'. unfold gmo in G.
  destruct H as [[E1 E2] | [[E1 E2] | [E1 E2]]]; subst; destruct s'; simpl in *;
    try contradiction; lia.
Qed.

Lemma fault_run_load_value : forall b r s, is_read r -> In r E0 -> rf s b r ->
    L1_abstract_erasure.C4_source Ev unit is_write touches gmo po E0 b r s.
Proof.
  intros b r s _ _ H. destruct b.
  unfold L1_abstract_erasure.C4_source, L1_abstract_erasure.cand.
  destruct H as [[E1 E2] | [[E1 E2] | [E1 E2]]]; subst;
  (split; [ repeat split; simpl; unfold E0, gmo; simpl; try tauto; left; lia |]);
  intros s' [Is' [Ws' [_ O]]]; unfold gmo, po in *;
  destruct s'; simpl in *; try contradiction; try (left; reflexivity); try (right; lia);
  destruct O; try contradiction; lia.
Qed.

Theorem fault_run_perbyte :
  forall b e, ~ clos_trans Ev (CfB Ev unit gmo is_write is_read touches E0 rf poloc b) e e.
Proof.
  intro b. apply rank_acyclic. intros a c H.
  destruct H as [[b' Hco] | [[b' [Ra [s [[_ Hrf] Hco]]]] | [[b' [_ Hrf]] | [Hpl _]]]].
  - destruct Hco as [_ [_ [_ [_ [_ [_ G]]]]]]. exact G.
  - destruct Hco as [_ [_ [_ [Wc [_ [_ G]]]]]]. destruct b'. exact (fr_rank a s c Hrf G Wc).
  - destruct Hrf as [[E1 E2] | [[E1 E2] | [E1 E2]]]; subst; simpl; lia.
  - exact (po_rank a c Hpl).
Qed.

Theorem fault_run_mainmodel :
  forall e, ~ clos_trans Ev
    (Frozen_mainmodel.FRf Ev unit nat gmo is_write is_read is_read is_write touches
       same_addr nodep nodep nodep nodep hart E0 rf po) e e.
Proof.
  apply rank_acyclic. intros a c H.
  unfold Frozen_mainmodel.FRf, Rlift_mainmodel.Rf in H.
  destruct H as [[b' Hco] | [[b' [Ra [s [Hrf Hco]]]] | [Hrfe | Hpp]]].
  - destruct Hco as [_ [_ [_ [_ [_ [_ G]]]]]]. exact G.
  - destruct Hco as [_ [_ [_ [Wc [_ [_ G]]]]]]. destruct b'. exact (fr_rank a s c Hrf G Wc).
  - destruct Hrfe as [b' [Hrf _]].
    destruct Hrf as [[E1 E2] | [[E1 E2] | [E1 E2]]]; subst; simpl; lia.
  - unfold Frozen_mainmodel.fault_ppo in Hpp. destruct Hpp as [Hp | [bx Hr2]].
    + destruct Hp as [a c P _ _ | a c Hf | a c Hf | a c Hf | a c Hf _ | a c _ [m [P1 [P2 _]]]
                     | a c _ [m [bb [P1 [P2 _]]]]];
        try contradiction.
      * exact (po_rank a c P).
      * pose proof (po_rank a m P1). pose proof (po_rank m c P2). lia.
      * pose proof (po_rank a m P1). pose proof (po_rank m c P2). lia.
    + destruct Hr2 as [[_ [_ [_ [_ [P _]]]]] _]. exact (po_rank a c P).
Qed.

(* the lane pair (K,D): every lane premise of Theorem 1 except gamma_adj *)
Theorem fault_run_lane_premises :
  In K E0 /\ In D E0 /\ is_write K /\ is_write D /\ gmo K D /\ po K D /\ hart D = hart K /\
  (forall b, touches D b -> touches K b) /\
  (forall b, touches D b -> wval K b = wval D b) /\
  (forall a c xb, is_read a -> touches a xb -> touches D xb -> po a D -> po D c -> po a K /\ po K c) /\
  (forall a c bb, po a K -> po K c -> (nodep a K \/ nodep a K) -> rf D bb c ->
     po a D /\ po D c /\ (nodep a D \/ nodep a D)).
Proof.
  split; [simpl; tauto |]. split; [simpl; tauto |].
  split; [exact I |]. split; [exact I |]. split; [unfold gmo; simpl; lia |].
  split; [exact I |]. split; [reflexivity |].
  split; [intros; exact I |]. split; [intros; reflexivity |].
  split.
  - intros a c xb Ra _ _ Pad _. destruct a; simpl in *; contradiction.
  - intros a c bb Pak _ _ _. destruct a; simpl in *; contradiction.
Qed.

Theorem fault_run_not_adj :
  ~ (forall b, touches D b ->
       forall s, In s E0 -> is_write s -> touches s b -> ~ (gmo K s /\ gmo s D)).
Proof.
  intro H. apply (H tt I W); [simpl; tauto | exact I | exact I |].
  unfold gmo; simpl; split; lia.
Qed.

Theorem fault_run_reads_121 :
  rf K tt Q1 /\ rf W tt Q2 /\ rf D tt Q3 /\
  wval K tt = 1 /\ wval W tt = 2 /\ wval D tt = 1.
Proof. unfold rf. repeat split; auto. Qed.

(* ==================================================================================================
   HEADLINE
   ================================================================================================== *)

Theorem gamma_adj_needed_obs :
  (* the faulting run is consistent ... *)
  (forall b r s, is_read r -> In r E0 -> rf s b r ->
     L1_abstract_erasure.C4_source Ev unit is_write touches gmo po E0 b r s) /\
  (forall b e, ~ clos_trans Ev (CfB Ev unit gmo is_write is_read touches E0 rf poloc b) e e) /\
  (forall e, ~ clos_trans Ev
     (Frozen_mainmodel.FRf Ev unit nat gmo is_write is_read is_read is_write touches
        same_addr nodep nodep nodep nodep hart E0 rf po) e e) /\
  (* ... gamma_adj fails for its lane pair ... *)
  ~ (forall b, touches D b ->
       forall s, In s E0 -> is_write s -> touches s b -> ~ (gmo K s /\ gmo s D)) /\
  (* ... and the reader sees 1, 2, 1 *)
  (rf K tt Q1 /\ rf W tt Q2 /\ rf D tt Q3 /\ wval K tt = 1 /\ wval W tt = 2 /\ wval D tt = 1) /\
  (* no candidate in which 1 and 2 are each written once lets three po-ordered reads see 1, 2, 1 *)
  (forall (Event Byte Value : Type) (gmo' : Event -> Event -> Prop) (is_write' is_read' : Event -> Prop)
          (touches' : Event -> Byte -> Prop) (E : list Event) (rf' : Event -> Byte -> Event -> Prop)
          (poloc' : Event -> Event -> Prop) (wval' : Event -> Byte -> Value)
          (x : Byte) (k w q1 q2 q3 : Event) (v1 v2 : Value),
     (In k E /\ is_write' k /\ touches' k x) ->
     (In w E /\ is_write' w /\ touches' w x) -> k <> w ->
     (forall a b, In a E -> In b E -> a <> b -> gmo' a b \/ gmo' b a) ->
     (forall e, In e E -> is_write' e -> touches' e x -> wval' e x = v1 -> e = k) ->
     (forall e, In e E -> is_write' e -> touches' e x -> wval' e x = v2 -> e = w) ->
     (forall e r, rf' e x r -> In e E /\ is_write' e /\ touches' e x) ->
     (is_read' q1 /\ is_read' q2 /\ is_read' q3 /\ touches' q1 x /\ touches' q2 x /\ touches' q3 x) ->
     (poloc' q1 q2 /\ poloc' q2 q3) ->
     (exists s1, rf' s1 x q1 /\ wval' s1 x = v1) ->
     (exists s2, rf' s2 x q2 /\ wval' s2 x = v2) ->
     (exists s3, rf' s3 x q3 /\ wval' s3 x = v1) ->
     exists e, clos_trans Event (CfB Event Byte gmo' is_write' is_read' touches' E rf' poloc' x) e e).
Proof.
  split; [exact fault_run_load_value |].
  split; [exact fault_run_perbyte |].
  split; [exact fault_run_mainmodel |].
  split; [exact fault_run_not_adj |].
  split; [exact fault_run_reads_121 |].
  intros Event Byte Value gmo' is_write' is_read' touches' E rf' poloc' wval' x k w q1 q2 q3 v1 v2
         H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
  exact (single_write_no_121 Event Byte Value gmo' is_write' is_read' touches' E rf' poloc' wval'
           x k w q1 q2 q3 v1 v2 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12).
Qed.
