(* PPO_union.v — RESTART-V M4: the frozen PPO union and its single edge-lift, discharging the
   `ppo_lifts` obligation of Rlift_mainmodel.

   PPO_frozen.v proves each frozen-active rule lifts (r1/r4/r9/r10/r11/r13 syntactic; r12 equal-
   duplicate; r2 = polnw \ rsw with the correct polarity). This file unions the 8 active rules into
   one witness relation `ppo_wit` and proves `ppo_wit_lifts : ppo_wit x y -> clos_trans Rf x y` — the
   exact shape Rlift_mainmodel.`witness_mainmodel_acyclic` takes as its `ppo_lifts` premise — and
   `ppo_wit_in_gmo` (forward). So the main-model witness acyclicity's last edge-kind obligation is
   discharged for the frozen fragment, modulo the per-rule modelling hypotheses (po-twin, rf
   functionality, duplicate footprint/deps, and the fault rules ⊆ Rf/gmo), which are the explicit
   RO/token adapter obligations (web-Pro #3: po-twin especially must be an explicit adapter theorem).

   Self-contained; 0 Admitted / 0 axioms (Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Import ListNotations.

Section PPOUnion.

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte : Type.
  Variable po : Event -> Event -> Prop.
  Variable is_load is_store is_read is_write : Event -> Prop.
  Variable same_addr : Event -> Event -> Prop.
  Variable addr data ctrl fence : Event -> Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable E0 : list Event.
  Variable Rf gmo : Event -> Event -> Prop.
  Variables d k : Event.

  Definition survivor (x : Event) : Prop := In x E0 /\ x <> d.
  Definition rf_ret (w : Event) (b : Byte) (r : Event) : Prop :=
    (rf w b r /\ ~ rf d b r) \/ (rf d b r /\ w = k).

  (* ---- fault PPO rules (frozen active) as targets in Rf / gmo ---- *)
  Inductive ppoF : Event -> Event -> Prop :=
  | fr1  : forall a b, po a b -> same_addr a b -> is_store b -> ppoF a b
  | fr4  : forall a b, fence a b -> ppoF a b
  | fr9  : forall a b, addr a b -> ppoF a b
  | fr10 : forall a b, data a b -> ppoF a b
  | fr11 : forall a b, ctrl a b -> is_store b -> ppoF a b
  | fr13 : forall a b, is_store b -> (exists m, po a m /\ po m b /\ addr a m) -> ppoF a b
  | fr12 : forall a b, is_load b ->
             (exists m bb, po a m /\ po m b /\ (addr a m \/ data a m) /\ rf m bb b) -> ppoF a b.

  (* r2 fault/witness (correct polarity: polnw minus same-source rsw) *)
  Definition store_between_F (x : Byte) (a b : Event) : Prop :=
    exists w, In w E0 /\ is_write w /\ touches w x /\ po a w /\ po w b.
  Definition store_between_N (x : Byte) (a b : Event) : Prop :=
    exists w, survivor w /\ is_write w /\ touches w x /\ po a w /\ po w b.
  Definition polnw_F (x : Byte) (a b : Event) : Prop :=
    is_read a /\ is_read b /\ touches a x /\ touches b x /\ po a b /\ ~ store_between_F x a b.
  Definition polnw_N (x : Byte) (a b : Event) : Prop :=
    is_read a /\ is_read b /\ touches a x /\ touches b x /\ po a b /\
    survivor a /\ survivor b /\ ~ store_between_N x a b.
  Definition rsw_F (x : Byte) (a b : Event) : Prop := exists w, rf w x a /\ rf w x b.
  Definition rsw_N (x : Byte) (a b : Event) : Prop := exists w, rf_ret w x a /\ rf_ret w x b.
  Definition r2F (x : Byte) (a b : Event) : Prop := polnw_F x a b /\ ~ rsw_F x a b.
  Definition r2N (x : Byte) (a b : Event) : Prop := polnw_N x a b /\ ~ rsw_N x a b.

  (* ---- the frozen witness PPO union ---- *)
  Inductive ppo_wit : Event -> Event -> Prop :=
  | pw1  : forall a b, survivor a -> survivor b -> po a b -> same_addr a b -> is_store b -> ppo_wit a b
  | pw4  : forall a b, survivor a -> survivor b -> fence a b -> ppo_wit a b
  | pw9  : forall a b, survivor a -> survivor b -> addr a b -> ppo_wit a b
  | pw10 : forall a b, survivor a -> survivor b -> data a b -> ppo_wit a b
  | pw11 : forall a b, survivor a -> survivor b -> ctrl a b -> is_store b -> ppo_wit a b
  | pw13 : forall a b, survivor a -> survivor b -> is_store b ->
             (exists m, survivor m /\ po a m /\ po m b /\ addr a m) -> ppo_wit a b
  | pw12 : forall a b, survivor a -> survivor b -> is_load b ->
             (exists m bb, po a m /\ po m b /\ (addr a m \/ data a m) /\ rf_ret m bb b) -> ppo_wit a b
  | pw2  : forall x a b, r2N x a b -> ppo_wit a b.

  (* ---- modelling hypotheses (the explicit RO/token adapter obligations) ---- *)
  Hypothesis ppoF_in_Rf  : forall x y, ppoF x y -> Rf x y.
  Hypothesis ppoF_in_gmo : forall x y, ppoF x y -> gmo x y.
  Hypothesis k_in    : In k E0.
  Hypothesis k_w     : is_write k.
  Hypothesis kd_ne   : k <> d.
  Hypothesis foot_dk : forall x, touches d x -> touches k x.
  Hypothesis po_twin : forall a b x,
    is_read a -> touches a x -> touches d x -> po a d -> po d b -> po a k /\ po k b.
  Hypothesis rf_functional : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.
  Hypothesis dup_r12 : forall a b bb,
      po a k -> po k b -> (addr a k \/ data a k) -> rf d bb b ->
      po a d /\ po d b /\ (addr a d \/ data a d).

  (* r2 lift lemmas (as in PPO_frozen, needed for pw2) *)
  Lemma polnw_lift : forall x a b, polnw_N x a b -> polnw_F x a b.
  Proof.
    intros x a b [Ra [Rb [Tax [Tbx [Pab [Sa [Sb Hnb]]]]]]].
    split; [exact Ra|]. split; [exact Rb|]. split; [exact Tax|]. split; [exact Tbx|].
    split; [exact Pab|]. intro Hsb. apply Hnb.
    destruct Hsb as [w [Inw [Ww [Twx [Paw Pwb]]]]].
    destruct (eq_ev_dec w d) as [Ewd | Nwd].
    - subst w. exists k. split; [split; [exact k_in | exact kd_ne]|].
      split; [exact k_w|]. split; [apply foot_dk; exact Twx|].
      destruct (po_twin a b x Ra Tax Twx Paw Pwb) as [Pak Pkb]. split; [exact Pak | exact Pkb].
    - exists w. split; [split; [exact Inw | exact Nwd]|].
      split; [exact Ww|]. split; [exact Twx|]. split; [exact Paw | exact Pwb].
  Qed.

  Lemma rsw_mono : forall x a b, rsw_F x a b -> rsw_N x a b.
  Proof.
    intros x a b [w [Rwa Rwb]].
    destruct (eq_ev_dec w d) as [Ewd | Nwd].
    - subst w. exists k. split; right; (split; [assumption | reflexivity]).
    - exists w. split; left; (split; [assumption|]);
        intro Hda; apply Nwd; symmetry; [ apply (rf_functional d w x a Hda Rwa)
                                        | apply (rf_functional d w x b Hda Rwb) ].
  Qed.

  Lemma r2N_sub_r2F : forall x a b, r2N x a b -> r2F x a b.
  Proof.
    intros x a b [Hp Hn]. split; [apply polnw_lift; exact Hp|].
    intro Hrsw. apply Hn. apply rsw_mono; exact Hrsw.
  Qed.

  (* the fault r2 edge is a fault ppo edge → in Rf / gmo. We expose r2F ⊆ Rf/gmo via ppoF is not
     directly possible (ppoF has no r2 constructor); take them as the same RO interface facts. *)
  Hypothesis r2F_in_Rf  : forall x a b, r2F x a b -> Rf a b.
  Hypothesis r2F_in_gmo : forall x a b, r2F x a b -> gmo a b.

  (* ---- the single union lift: ppo_wit x y ⇒ a fault-run path (here length-1) ---- *)
  Theorem ppo_wit_lifts : forall x y, ppo_wit x y -> clos_trans Event Rf x y.
  Proof.
    intros x y H. apply t_step. destruct H.
    - apply ppoF_in_Rf. apply fr1; assumption.
    - apply ppoF_in_Rf. apply fr4; assumption.
    - apply ppoF_in_Rf. apply fr9; assumption.
    - apply ppoF_in_Rf. apply fr10; assumption.
    - apply ppoF_in_Rf. apply fr11; assumption.
    - apply ppoF_in_Rf. apply fr13; [assumption|].
      destruct H2 as [m [_ [Pam [Pmb Aam]]]]. exists m; auto.
    - apply ppoF_in_Rf. apply fr12; [assumption|].
      destruct H2 as [m [bb [Pam [Pmb [Hdep Hrf]]]]].
      unfold rf_ret in Hrf. destruct Hrf as [[Hrf1 _] | [Hrfd Hmk]].
      + exists m, bb. split; [exact Pam|]. split; [exact Pmb|]. split; [exact Hdep|]. exact Hrf1.
      + subst m. destruct (dup_r12 a b bb Pam Pmb Hdep Hrfd) as [Pad [Pdb Hdepd]].
        exists d, bb. split; [exact Pad|]. split; [exact Pdb|]. split; [exact Hdepd|]. exact Hrfd.
    - apply (r2F_in_Rf x). apply r2N_sub_r2F; exact H.
  Qed.

  Theorem ppo_wit_in_gmo : forall x y, ppo_wit x y -> gmo x y.
  Proof.
    intros x y H. destruct H.
    - apply ppoF_in_gmo. apply fr1; assumption.
    - apply ppoF_in_gmo. apply fr4; assumption.
    - apply ppoF_in_gmo. apply fr9; assumption.
    - apply ppoF_in_gmo. apply fr10; assumption.
    - apply ppoF_in_gmo. apply fr11; assumption.
    - apply ppoF_in_gmo. apply fr13; [assumption|].
      destruct H2 as [m [_ [Pam [Pmb Aam]]]]. exists m; auto.
    - apply ppoF_in_gmo. apply fr12; [assumption|].
      destruct H2 as [m [bb [Pam [Pmb [Hdep Hrf]]]]].
      unfold rf_ret in Hrf. destruct Hrf as [[Hrf1 _] | [Hrfd Hmk]].
      + exists m, bb. split; [exact Pam|]. split; [exact Pmb|]. split; [exact Hdep|]. exact Hrf1.
      + subst m. destruct (dup_r12 a b bb Pam Pmb Hdep Hrfd) as [Pad [Pdb Hdepd]].
        exists d, bb. split; [exact Pad|]. split; [exact Pdb|]. split; [exact Hdepd|]. exact Hrfd.
    - apply (r2F_in_gmo x). apply r2N_sub_r2F; exact H.
  Qed.

End PPOUnion.
