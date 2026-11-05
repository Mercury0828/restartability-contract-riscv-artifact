(* PPO_frozen.v — RESTART-V M4: concrete PPO edge-lift for the FROZEN fragment (discharges the
   `ppo_lifts` obligation of Rlift_mainmodel). web-Pro #2's highest-leverage step.

   RVWMO preserved program order has 13 rules. For the frozen instruction family (one unit-stride
   vector store, a fixed M-mode handler, no AMO/SC, no acquire/release annotations) the rules split:

     - EMPTY (no inhabitants): r3 (AMO/SC forward), r5/r6/r7/r8 (acquire/release/RCsc/RCpc, pairing).
     - SYNTACTIC / local (this file): r1 (overlapping-addr, b store), r4 (fence order), r9/r10/r11
       (address/data/control dependency), r13 (b a STORE with an intermediate addr-dependent
       store). These are built from po + syntactic dependency relations + is_load/is_store/same_addr,
       which erasure (delete d, retarget rf d→k) does NOT change — it only alters rf. So a witness
       edge among survivors is literally a fault edge; the lift is length-1.
     - rf-DEPENDENT (r2, r12): handled separately (r12 next; r2 is the rsw-monotonicity case web-Pro
       flagged) — NOT in this file yet.

   The key modelling fact this file uses: witness po / addr / data / ctrl / fence / same_addr /
   is_load / is_store are the fault ones restricted to survivors (erasure-invariance of syntactic
   structure). Under that, every syntactic/r13 witness edge lifts to a single fault ppo edge, which
   is in the main-model union Rf. Self-contained; 0 Admitted / 0 axioms (Print Assumptions). Coq 8.15.

   Frozen-PPO status table (theorem-cited):
     r1  active  — ppoN_lifts / nr1     r2  rf-dep  — PENDING (rsw monotonicity)
     r3  EMPTY                          r4  active  — ppoN_lifts / nr4
     r5  EMPTY   r6 EMPTY  r7 EMPTY  r8 EMPTY
     r9  active  — ppoN_lifts / nr9     r10 active  — ppoN_lifts / nr10
     r11 active  — ppoN_lifts / nr11    r12 rf-dep  — PENDING (equal-duplicate path)
     r13 active  — ppoN_lifts / nr13                                                     *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Import ListNotations.

Section PPOFrozen.

  Variable Event : Type.
  Variable po : Event -> Event -> Prop.
  Variable is_load is_store : Event -> Prop.
  Variable same_addr : Event -> Event -> Prop.
  Variable addr data ctrl fence : Event -> Event -> Prop.  (* syntactic: b depends on / ordered after a *)
  Variable survivor : Event -> Prop.
  Variable Rf : Event -> Event -> Prop.                     (* fault main-model union; ppoF ⊆ Rf *)

  (* Frozen active fault PPO rules (empty rules omitted; rf-dependent r2/r12 not here). *)
  Inductive ppoF : Event -> Event -> Prop :=
  | fr1  : forall a b, po a b -> same_addr a b -> is_store b -> ppoF a b
  | fr4  : forall a b, fence a b -> ppoF a b
  | fr9  : forall a b, addr a b -> ppoF a b
  | fr10 : forall a b, data a b -> ppoF a b
  | fr11 : forall a b, ctrl a b -> is_store b -> ppoF a b
  | fr13 : forall a b, is_store b -> (exists m, po a m /\ po m b /\ addr a m) -> ppoF a b.

  Hypothesis ppoF_in_Rf : forall x y, ppoF x y -> Rf x y.

  (* Witness PPO for the syntactic/r13 rules: the same rules, over survivor events. The syntactic
     relations are erasure-invariant, so each witness edge exhibits a fault edge. *)
  Inductive ppoN : Event -> Event -> Prop :=
  | nr1  : forall a b, survivor a -> survivor b -> po a b -> same_addr a b -> is_store b -> ppoN a b
  | nr4  : forall a b, survivor a -> survivor b -> fence a b -> ppoN a b
  | nr9  : forall a b, survivor a -> survivor b -> addr a b -> ppoN a b
  | nr10 : forall a b, survivor a -> survivor b -> data a b -> ppoN a b
  | nr11 : forall a b, survivor a -> survivor b -> ctrl a b -> is_store b -> ppoN a b
  | nr13 : forall a b, survivor a -> survivor b -> is_store b ->
             (exists m, survivor m /\ po a m /\ po m b /\ addr a m) -> ppoN a b.

  (* Each witness syntactic/r13 edge lifts to a length-1 fault-run path. *)
  Theorem ppoN_lifts : forall x y, ppoN x y -> clos_trans Event Rf x y.
  Proof.
    intros x y H. apply t_step. apply ppoF_in_Rf. destruct H.
    - apply fr1; assumption.
    - apply fr4; assumption.
    - apply fr9; assumption.
    - apply fr10; assumption.
    - apply fr11; assumption.
    - apply fr13; [assumption|]. destruct H2 as [m [_ [Pam [Pmb Aam]]]]. exists m; auto.
  Qed.

  (* Forward direction (ppo_N ⊆ gmo_N) for the syntactic/r13 rules: reduces to fault ppo ⊆ gmo (an
     antecedent of fault consistency) since the witness edge IS a fault edge and gmo is unchanged on
     survivors. Stated against a fault ppo⊆gmo interface. *)
  Variable gmo : Event -> Event -> Prop.
  Hypothesis ppoF_in_gmo : forall x y, ppoF x y -> gmo x y.

  Theorem ppoN_in_gmo : forall x y, ppoN x y -> gmo x y.
  Proof.
    intros x y H. apply ppoF_in_gmo. destruct H.
    - apply fr1; assumption.
    - apply fr4; assumption.
    - apply fr9; assumption.
    - apply fr10; assumption.
    - apply fr11; assumption.
    - apply fr13; [assumption|]. destruct H2 as [m [_ [Pam [Pmb Aam]]]]. exists m; auto.
  Qed.

End PPOFrozen.

(* ---------------- r12: pipeline dependency through an addr/data-dependent store the load reads ----
   b is a load; a store m lies po-between a and b, m has an address or data dependency on a, and b
   reads-from m. Under erasure the load may have been retargeted d→k, so the WITNESS witnesses r12 via
   m = k while the FAULT run witnesses it via m = d. The ppo EDGE a→b is the same; the lift is still
   length-1, using that the keeper k inherits the deleted duplicate d's r12-intermediate role (same
   static store instance: same dependency on a and same po-position between a and b). *)
Section R12.

  Variable Event : Type.
  Variable Byte : Type.
  Variable po : Event -> Event -> Prop.
  Variable is_load : Event -> Prop.
  Variable addr data : Event -> Event -> Prop.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable Rf : Event -> Event -> Prop.
  Variables d k : Event.

  Definition rf_ret (w : Event) (b : Byte) (r : Event) : Prop :=
    (rf w b r /\ ~ rf d b r) \/ (rf d b r /\ w = k).

  Definition r12F (a b : Event) : Prop :=
    is_load b /\ exists m bb, po a m /\ po m b /\ (addr a m \/ data a m) /\ rf m bb b.
  Definition r12N (a b : Event) : Prop :=
    is_load b /\ exists m bb, po a m /\ po m b /\ (addr a m \/ data a m) /\ rf_ret m bb b.

  Hypothesis r12F_in_Rf : forall a b, r12F a b -> Rf a b.
  (* duplicate-structure commitment: k inherits d's role as an r12 intermediate. *)
  Hypothesis dup_r12 : forall a b bb,
      po a k -> po k b -> (addr a k \/ data a k) -> rf d bb b ->
      po a d /\ po d b /\ (addr a d \/ data a d).

  Theorem r12N_lifts : forall a b, r12N a b -> clos_trans Event Rf a b.
  Proof.
    intros a b [Hlb [m [bb [Pam [Pmb [Hdep Hrf]]]]]].
    apply t_step. apply r12F_in_Rf. split; [exact Hlb|].
    unfold rf_ret in Hrf. destruct Hrf as [[Hrf1 _] | [Hrfd Hmk]].
    - (* source unchanged: the witness intermediate m is a fault intermediate *)
      exists m, bb. split; [exact Pam|]. split; [exact Pmb|]. split; [exact Hdep|]. exact Hrf1.
    - (* retargeted d->k: the fault run witnesses r12 via the deleted duplicate d *)
      subst m. destruct (dup_r12 a b bb Pam Pmb Hdep Hrfd) as [Pad [Pdb Hdepd]].
      exists d, bb. split; [exact Pad|]. split; [exact Pdb|]. split; [exact Hdepd|]. exact Hrfd.
  Qed.

End R12.

(* ---------------- r2: same-address program-ordered loads reading DIFFERENT memory operations ------
   RVWMO r2 = ([R]; po-loc-no-intervening-write; [R]) \ rsw,  rsw = rf^-1 ; rf  (SAME source).
   The set-difference polarity is the crux (web-Pro #3): r2 fires when the two loads read DIFFERENT
   writes; same-source pairs are SUBTRACTED. So under erasure, retargeting reads d->k can only MERGE
   sources (grow rsw), hence r2 can only SHRINK — every witness r2 edge is already a fault r2 edge:
       r2_N  ⊆  r2_F ↾ survivors.
   Proof = polnw inclusion (Lemma polnw_lift, using the po-TWIN property: a deleted intervening store
   d has a surviving same-byte twin k at the same po-cut) + rsw monotonicity (Lemma rsw_mono, source
   contraction ρ(d)=k merges, never separates). This gives BOTH the single-edge lift and gmo-forward.
   No gamma_adj needed (that belongs to C4/fr/final-memory). Keeper = coherence-earlier duplicate. *)
Section R2.

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte : Type.
  Variable po : Event -> Event -> Prop.
  Variable is_read is_write : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable E0 : list Event.
  Variable Rf gmo : Event -> Event -> Prop.
  Variables d k : Event.

  Definition survivorR (x : Event) : Prop := In x E0 /\ x <> d.
  Definition rf_ret2 (w : Event) (x : Byte) (r : Event) : Prop :=
    (rf w x r /\ ~ rf d x r) \/ (rf d x r /\ w = k).

  Definition store_between_F (x : Byte) (a b : Event) : Prop :=
    exists w, In w E0 /\ is_write w /\ touches w x /\ po a w /\ po w b.
  Definition store_between_N (x : Byte) (a b : Event) : Prop :=
    exists w, survivorR w /\ is_write w /\ touches w x /\ po a w /\ po w b.

  Definition polnw_F (x : Byte) (a b : Event) : Prop :=
    is_read a /\ is_read b /\ touches a x /\ touches b x /\ po a b /\ ~ store_between_F x a b.
  Definition polnw_N (x : Byte) (a b : Event) : Prop :=
    is_read a /\ is_read b /\ touches a x /\ touches b x /\ po a b /\
    survivorR a /\ survivorR b /\ ~ store_between_N x a b.

  Definition rsw_F (x : Byte) (a b : Event) : Prop := exists w, rf w x a /\ rf w x b.
  Definition rsw_N (x : Byte) (a b : Event) : Prop := exists w, rf_ret2 w x a /\ rf_ret2 w x b.

  Definition r2F (x : Byte) (a b : Event) : Prop := polnw_F x a b /\ ~ rsw_F x a b.
  Definition r2N (x : Byte) (a b : Event) : Prop := polnw_N x a b /\ ~ rsw_N x a b.

  (* duplicate-structure commitments (explicit, per web-Pro #3: the RO adapter must supply the full
     po-twin property, not a vague envelope). *)
  Hypothesis k_in    : In k E0.
  Hypothesis k_w     : is_write k.
  Hypothesis kd_ne   : k <> d.
  Hypothesis foot_dk : forall x, touches d x -> touches k x.
  Hypothesis po_twin : forall a b x,
    is_read a -> touches a x -> touches d x -> po a d -> po d b -> po a k /\ po k b.
  Hypothesis rf_functional : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.

  (* Lemma 1: witness polnw implies fault polnw (a deleted intervening store has a surviving twin). *)
  Lemma polnw_lift : forall x a b, polnw_N x a b -> polnw_F x a b.
  Proof.
    intros x a b [Ra [Rb [Tax [Tbx [Pab [Sa [Sb Hnb]]]]]]].
    split; [exact Ra|]. split; [exact Rb|]. split; [exact Tax|]. split; [exact Tbx|].
    split; [exact Pab|].
    intro Hsb. apply Hnb. destruct Hsb as [w [Inw [Ww [Twx [Paw Pwb]]]]].
    destruct (eq_ev_dec w d) as [Ewd | Nwd].
    - subst w. exists k. split; [split; [exact k_in | exact kd_ne]|].
      split; [exact k_w|]. split; [apply foot_dk; exact Twx|].
      destruct (po_twin a b x Ra Tax Twx Paw Pwb) as [Pak Pkb]. split; [exact Pak | exact Pkb].
    - exists w. split; [split; [exact Inw | exact Nwd]|].
      split; [exact Ww|]. split; [exact Twx|]. split; [exact Paw | exact Pwb].
  Qed.

  (* Lemma 2: source contraction only grows rsw (never separates a shared-source pair). *)
  Lemma rsw_mono : forall x a b, rsw_F x a b -> rsw_N x a b.
  Proof.
    intros x a b [w [Rwa Rwb]].
    destruct (eq_ev_dec w d) as [Ewd | Nwd].
    - subst w. exists k. split; right; (split; [assumption | reflexivity]).
    - exists w. split; left; (split; [assumption|]);
        intro Hda; apply Nwd; symmetry; [ apply (rf_functional d w x a Hda Rwa)
                                        | apply (rf_functional d w x b Hda Rwb) ].
  Qed.

  Hypothesis r2F_in_Rf  : forall x a b, r2F x a b -> Rf a b.
  Hypothesis r2F_in_gmo : forall x a b, r2F x a b -> gmo a b.

  (* r2_N ⊆ r2_F : every witness r2 edge is already a fault r2 edge. *)
  Lemma r2N_sub_r2F : forall x a b, r2N x a b -> r2F x a b.
  Proof.
    intros x a b [Hpolnw Hnrsw]. split.
    - apply polnw_lift; exact Hpolnw.
    - intro Hrsw. apply Hnrsw. apply rsw_mono; exact Hrsw.
  Qed.

  Theorem r2N_lifts : forall x a b, r2N x a b -> clos_trans Event Rf a b.
  Proof. intros x a b H. apply t_step. apply (r2F_in_Rf x). apply r2N_sub_r2F; exact H. Qed.

  Theorem r2N_in_gmo : forall x a b, r2N x a b -> gmo a b.
  Proof. intros x a b H. apply (r2F_in_gmo x). apply r2N_sub_r2F; exact H. Qed.

  (* Polarity sanity check (web-Pro #3 required guard): same-source pairs are NOT r2. *)
  Lemma rsw_not_r2F : forall x a b, rsw_F x a b -> ~ r2F x a b.
  Proof. intros x a b Hrsw [_ Hnrsw]. apply Hnrsw; exact Hrsw. Qed.
  Lemma rsw_not_r2N : forall x a b, rsw_N x a b -> ~ r2N x a b.
  Proof. intros x a b Hrsw [_ Hnrsw]. apply Hnrsw; exact Hrsw. Qed.

End R2.

