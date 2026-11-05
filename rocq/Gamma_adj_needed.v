(* Gamma_adj_needed.v — RESTART-V: gamma_adj cannot be dropped from the erasure.

   A three-write run at one byte: the keeper K and the replay D are an equal-valued duplicate pair,
   and a write W of another value lies coherence-between them (K < W < D). Every premise of
   `Obs_final_state.final_state_preserved_exists` holds except gamma_adj, and its conclusion fails:
   the fault run's final value is D's (1), while every coherence-maximal survivor of the erasure
   carries W's value (2). So without gamma_adj, erasing the replay changes the final memory.

   0 Admitted / 0 axioms. Modifies no existing .v file. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import RestartV.Obs_final_state.
Import ListNotations.

Inductive Ev := K | W | D.

Definition ev_eq_dec : forall x y : Ev, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition rank (e : Ev) : nat := match e with K => 0 | W => 1 | D => 2 end.
Definition gmo (x y : Ev) : Prop := rank x < rank y.
Definition is_write (_ : Ev) : Prop := True.
Definition touches (_ : Ev) (_ : unit) : Prop := True.
Definition wval (e : Ev) (_ : unit) : nat := match e with W => 2 | _ => 1 end.
Definition E0 : list Ev := [K; W; D].

Lemma g_wf : gmo_wf Ev gmo E0.
Proof.
  constructor.
  - intros e _. unfold gmo. lia.
  - intros a b c _ _ _. unfold gmo. lia.
  - intros a b _ _ H. unfold gmo.
    destruct a, b; simpl; try lia; exfalso; apply H; reflexivity.
Qed.

(* the duplicate-pair premises other than gamma_adj all hold *)
Lemma g_k_in : In K E0.
Proof. simpl; tauto. Qed.
Lemma g_kd_ne : K <> D.
Proof. discriminate. Qed.
Lemma g_foot : forall b, touches D b -> touches K b.
Proof. intros b _; exact I. Qed.
Lemma g_dup : forall b, touches D b -> wval K b = wval D b.
Proof. intros b _; reflexivity. Qed.

(* gamma_adj fails: W lies coherence-between the keeper and the replay *)
Lemma g_not_adj :
  ~ (forall b, touches D b ->
       forall w, In w E0 -> is_write w -> touches w b -> ~ (gmo K w /\ gmo w D)).
Proof.
  intro H. apply (H tt I W); [simpl; tauto | exact I | exact I |].
  unfold gmo; simpl; lia.
Qed.

Theorem gamma_adj_needed :
  co_max_of Ev unit gmo is_write touches (inE0 Ev E0) tt D /\
  (forall w_n, co_max_of Ev unit gmo is_write touches (survivor Ev E0 D) tt w_n ->
               wval w_n tt <> wval D tt).
Proof.
  split.
  - split; [exact I|]. split; [exact I|]. split; [unfold inE0; simpl; tauto|].
    intros w' Hw' _ _. unfold inE0 in Hw'. simpl in Hw'.
    destruct Hw' as [E | [E | [E | []]]]; subst w';
      [right; unfold gmo; simpl; lia | right; unfold gmo; simpl; lia | left; reflexivity].
  - intros w_n [_ [_ [[Hin Hnd] Hmax]]].
    assert (HW : survivor Ev E0 D W) by (split; [simpl; tauto | discriminate]).
    destruct (Hmax W HW I I) as [E | G].
    + subst w_n. discriminate.
    + simpl in Hin. destruct Hin as [E | [E | [E | []]]]; subst w_n.
      * unfold gmo in G; simpl in G; lia.
      * discriminate.
      * exfalso; apply Hnd; reflexivity.
Qed.

(* the whole counterexample in one statement: every premise but gamma_adj, gamma_adj false,
   and the conclusion of final_state_preserved_exists false at the replay's co-max *)
Theorem gamma_adj_needed_full :
  gmo_wf Ev gmo E0 /\ In K E0 /\ is_write K /\ K <> D /\
  (forall b, touches D b -> touches K b) /\ (forall b, touches D b -> wval K b = wval D b) /\
  ~ (forall b, touches D b ->
       forall w, In w E0 -> is_write w -> touches w b -> ~ (gmo K w /\ gmo w D)) /\
  co_max_of Ev unit gmo is_write touches (inE0 Ev E0) tt D /\
  ~ (exists w_n, co_max_of Ev unit gmo is_write touches (survivor Ev E0 D) tt w_n /\
                 wval D tt = wval w_n tt).
Proof.
  destruct gamma_adj_needed as [Hmax Hno].
  refine (conj g_wf (conj g_k_in (conj I (conj g_kd_ne (conj g_foot (conj g_dup
            (conj g_not_adj (conj Hmax _)))))))).
  intros [w_n [Hc Hv]]. apply (Hno w_n Hc). symmetry; exact Hv.
Qed.
