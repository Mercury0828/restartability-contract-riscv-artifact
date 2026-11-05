(* CG2_concrete_instance.v — RESTART-V M4: CG-2 concrete-instantiation certificate.

   NON-VACUITY. `T1_frozen_instantiated.frozen_T1_refinement_instantiated` (the capstone) proves a
   conditional refinement out of ~30 premises. This file exhibits a CONCRETE finite execution — a
   7-event single-byte lane-3 slice of a VL=4,K=2,P={3} vector-store fault — that JOINTLY inhabits
   every premise, and APPLIES the capstone to it. So the premise set is a real execution, not an
   empty hypothesis set: `cg2_concrete_instance` is the capstone's conclusion, unconditionally, for
   this instance.

   THE MODEL. Ev = {Wi,K,D,Rp,Rs,Tr,Xr}. Byte = unit (the single duplicated lane-3 byte). Wi = the
   initial write; K = the first store attempt (keeper); D = the replay store (deleted duplicate,
   equal value); Rp = a read of the initial value; Rs = a read of the replay; Tr,Xr = the two
   footprint-clean trap-region context events (M-mode handler + mret — they touch NOTHING). po and
   gmo both coincide with rank<, so every acyclicity is a single rank-measure argument.

   The two repaired lemmas are EXERCISED, not vacuous: `rf_is_C4` drives retarget via the keeper's
   `po k d`; `footprint_read_not_in_trap` holds because Tr,Xr are the in-trap events but are NOT
   reads (the footprint-clean handler).

   0 Admitted / 0 axioms (Print Assumptions cg2_concrete_instance -> Closed under the global context).
   Modifies no existing .v file. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.micromega.Lia.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Rlift_mainmodel.
Require Import RestartV.PPO_union.
Require Import RestartV.Frozen_mainmodel.
Require Import RestartV.Obs_final_state.
Require Import RestartV.T1_frozen_instantiated.
Import ListNotations.

(* ============================ the concrete model ============================ *)

Inductive Ev := Wi | K | D | Rp | Rs | Tr | Xr.

Definition ev_eq_dec : forall x y : Ev, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition rank (e : Ev) : nat :=
  match e with Wi => 0 | Rp => 1 | K => 2 | Tr => 3 | Xr => 4 | D => 5 | Rs => 6 end.

Definition po  (a b : Ev) : Prop := rank a < rank b.
Definition gmo (a b : Ev) : Prop := rank a < rank b.

Definition is_write (e : Ev) : Prop := match e with Wi | K | D => True | _ => False end.
Definition is_read  (e : Ev) : Prop := match e with Rp | Rs => True | _ => False end.
Definition touches  (e : Ev) (_ : unit) : Prop := match e with Tr | Xr => False | _ => True end.
Definition wval     (e : Ev) (_ : unit) : nat  := match e with K | D => 7 | _ => 0 end.
Definition hart     (_ : Ev) : unit := tt.

Definition rf (w : Ev) (_ : unit) (r : Ev) : Prop :=
  match w with
  | Wi => match r with Rp => True | _ => False end
  | D  => match r with Rs => True | _ => False end
  | _  => False
  end.

Definition addr (_ _ : Ev) : Prop := False.
Definition data (_ _ : Ev) : Prop := False.
Definition ctrl (_ _ : Ev) : Prop := False.
Definition fence (_ _ : Ev) : Prop := False.
Definition same_addr (a b : Ev) : Prop := touches a tt /\ touches b tt.
Definition poloc (a b : Ev) : Prop := po a b /\ touches a tt /\ touches b tt.

Definition E0 : list Ev := [Wi; Rp; K; Tr; Xr; D; Rs].

Ltac inE0tac := simpl; repeat (first [ left; reflexivity | right ]).

(* ============================ the two acyclicity certificates ============================ *)
(* every model edge (co / fr / rf / poloc / ppoF / r2 / rfe) goes strictly low->high in rank. *)

Lemma ct_rank : forall (R : Ev -> Ev -> Prop),
  (forall x y, R x y -> rank x < rank y) ->
  forall x y, clos_trans Ev R x y -> rank x < rank y.
Proof.
  intros R Hedge x y Hct. induction Hct.
  - apply Hedge; assumption.
  - lia.
Qed.

Lemma acyc_from_rank : forall (R : Ev -> Ev -> Prop),
  (forall x y, R x y -> rank x < rank y) -> forall x, ~ clos_trans Ev R x x.
Proof. intros R Hedge x Hct. pose proof (ct_rank R Hedge x x Hct). lia. Qed.

(* the fr-edge sub-argument, shared by Cf and FRf: a read's source-write is rank-below the write
   the read is fr-before, and the read sits exactly one rank above its source. *)
Lemma fr_rank_lemma : forall (w1 x y : Ev) (b : unit),
  rf w1 b x -> is_write y -> gmo w1 y -> rank x < rank y.
Proof.
  intros w1 x y b Hrf Hw Hg. unfold gmo in Hg.
  destruct w1; simpl in Hrf; try contradiction;
  destruct x; simpl in Hrf; try contradiction;
  destruct y; simpl in Hw, Hg; try contradiction; simpl; lia.
Qed.

(* ppoF edges: only fr1 (po a b) is non-vacuous here; fence/addr/data/ctrl are empty. *)
Lemma ppoF_rank : forall x y,
  PPO_union.ppoF Ev unit po is_read is_write same_addr addr data ctrl fence rf x y ->
  rank x < rank y.
Proof.
  intros x y H.
  destruct H as [ a b Hpo Hsa Hst | a b Hf | a b Ha | a b Hd | a b Hc Hst
                | a b Hst Hex | a b Hlb Hex ].
  - unfold po in Hpo; exact Hpo.
  - destruct Hf.
  - destruct Ha.
  - destruct Hd.
  - destruct Hc.
  - destruct Hex as [m [_ [_ Ham]]]; destruct Ham.
  - destruct Hex as [m [bb [_ [_ [Hor _]]]]]; destruct Hor as [Ha | Hd]; [ destruct Ha | destruct Hd ].
Qed.

Definition CfC :=
  Clift_coherence.Cf Ev unit gmo is_write is_read touches E0 rf poloc.

Definition FRfC :=
  Frozen_mainmodel.FRf Ev unit unit gmo is_write is_read is_read is_write
    touches same_addr addr data ctrl fence hart E0 rf po.

Lemma edge_Cf : forall x y, CfC x y -> rank x < rank y.
Proof.
  intros x y H. unfold CfC, Clift_coherence.Cf in H.
  destruct H as [ [b Hco] | [ [b [Hrx Hfr]] | [ [b Hrf] | Hpl ] ] ].
  - unfold Clift_coherence.co_flt, Clift_coherence.coOn, Clift_coherence.inE0 in Hco.
    destruct Hco as [_ [_ [_ [_ [_ [_ G]]]]]]. unfold gmo in G; exact G.
  - unfold Clift_coherence.fr_flt in Hfr. destruct Hfr as [w1 [Hrf Hco]].
    unfold Clift_coherence.co_flt, Clift_coherence.coOn, Clift_coherence.inE0 in Hco.
    destruct Hco as [_ [_ [_ [Wy [_ [_ G]]]]]].
    exact (fr_rank_lemma w1 x y b Hrf Wy G).
  - destruct x; simpl in Hrf; try contradiction;
    destruct y; simpl in Hrf; try contradiction; simpl; lia.
  - unfold poloc in Hpl. destruct Hpl as [Hpo _]. unfold po in Hpo; exact Hpo.
Qed.

Lemma edge_FRf : forall x y, FRfC x y -> rank x < rank y.
Proof.
  intros x y H. unfold FRfC, Frozen_mainmodel.FRf, Rlift_mainmodel.Rf in H.
  destruct H as [ [b Hco] | [ [b [Hrx Hfr]] | [ Hrfe | Hppo ] ] ].
  - unfold Rlift_mainmodel.co_flt, Rlift_mainmodel.coOn, Rlift_mainmodel.inE0 in Hco.
    destruct Hco as [_ [_ [_ [_ [_ [_ G]]]]]]. unfold gmo in G; exact G.
  - unfold Rlift_mainmodel.fr_flt in Hfr. destruct Hfr as [w1 [Hrf Hco]].
    unfold Rlift_mainmodel.co_flt, Rlift_mainmodel.coOn, Rlift_mainmodel.inE0 in Hco.
    destruct Hco as [_ [_ [_ [Wy [_ [_ G]]]]]].
    exact (fr_rank_lemma w1 x y b Hrf Wy G).
  - unfold Rlift_mainmodel.rfe_flt in Hrfe. destruct Hrfe as [b [Hrf _]].
    destruct x; simpl in Hrf; try contradiction;
    destruct y; simpl in Hrf; try contradiction; simpl; lia.
  - unfold Frozen_mainmodel.fault_ppo in Hppo. destruct Hppo as [Hpf | [bx Hr2]].
    + exact (ppoF_rank x y Hpf).
    + unfold PPO_union.r2F, PPO_union.polnw_F in Hr2.
      destruct Hr2 as [[_ [_ [_ [_ [Hpo _]]]]] _]. unfold po in Hpo; exact Hpo.
Qed.

Definition Hcf  : forall x, ~ clos_trans Ev CfC  x x := acyc_from_rank CfC  edge_Cf.
Definition Hfrf : forall x, ~ clos_trans Ev FRfC x x := acyc_from_rank FRfC edge_FRf.

(* ============================ the ~30 premises, discharged concretely ============================ *)

Lemma h_Hirr : forall e, In e E0 -> ~ gmo e e.
Proof. intros e _ H. unfold gmo in H. lia. Qed.

Lemma h_Htr : forall a b c, In a E0 -> In b E0 -> In c E0 -> gmo a b -> gmo b c -> gmo a c.
Proof. intros a b c _ _ _ Hab Hbc. unfold gmo in *. lia. Qed.

Lemma h_Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.
Proof.
  intros a b _ _ Hne. unfold gmo.
  destruct a; destruct b; simpl; try lia; exfalso; apply Hne; reflexivity.
Qed.

Lemma h_din : In D E0.  Proof. inE0tac. Qed.
Lemma h_dw  : is_write D. Proof. exact I. Qed.
Lemma h_kin : In K E0.  Proof. inE0tac. Qed.
Lemma h_kw  : is_write K. Proof. exact I. Qed.
Lemma h_kdne : K <> D.   Proof. discriminate. Qed.
Lemma h_keeper : gmo K D. Proof. unfold gmo; simpl; lia. Qed.
Lemma h_pin : In K E0.  Proof. inE0tac. Qed.
Lemma h_qin : In D E0.  Proof. inE0tac. Qed.

Lemma h_Hdup : DupPair Ev unit nat is_write touches wval K D.
Proof.
  constructor.
  - exact I.
  - exact I.
  - intros b; split; intros _; exact I.
  - intros b _; reflexivity.
Qed.

Lemma h_Hro : RO_K Ev gmo po K D K.
Proof.
  constructor.
  - unfold L1_abstract_erasure.is_keeper. left; split; [ reflexivity | unfold gmo; simpl; lia ].
  - split; [ intros _; unfold po; simpl; lia | intros Hc; discriminate Hc ].
Qed.

Lemma h_Hdpq : D = K \/ D = D.  Proof. right; reflexivity. Qed.

Lemma h_Hgamma : forall b, gamma_adj Ev unit is_write touches E0 gmo b K D.
Proof.
  intros b Hex. unfold gamma_adj in Hex. destruct Hex as [z [Hin Hbet]].
  unfold L1_abstract_erasure.between in Hbet.
  destruct Hbet as [Wz [Tz [ZK [ZD Hor]]]].
  (* only z=Wi survives is_write z; z=K,z=D are killed by ZK:z<>K, ZD:z<>D *)
  destruct z; simpl in Wz; try contradiction;
    unfold gmo in Hor; destruct Hor as [[G _] | [G _]]; simpl in G; lia.
Qed.

Lemma h_dupval : forall b, touches D b -> wval K b = wval D b.
Proof. intros b _; reflexivity. Qed.

Lemma h_rfC4 : forall b r w, is_read r -> In r E0 -> rf w b r ->
  C4_source Ev unit is_write touches gmo po E0 b r w.
Proof.
  intros b r w Hr Hin Hrf.
  destruct r; simpl in Hr; try contradiction.
  - (* r = Rp : source Wi is the unique candidate *)
    destruct w; simpl in Hrf; try contradiction.
    unfold L1_abstract_erasure.C4_source. split.
    + unfold L1_abstract_erasure.cand.
      split; [ inE0tac | ]. split; [ exact I | ]. split; [ exact I | ].
      left; unfold gmo; simpl; lia.
    + intros w' Hc'. unfold L1_abstract_erasure.cand in Hc'.
      destruct Hc' as [Hin' [Ww' [Tw' Hord']]].
      destruct w'; simpl in Ww'; try contradiction.
      * left; reflexivity.
      * exfalso; unfold gmo, po in Hord'; simpl in Hord'; destruct Hord' as [G | G]; lia.
      * exfalso; unfold gmo, po in Hord'; simpl in Hord'; destruct Hord' as [G | G]; lia.
  - (* r = Rs : source D is coherence-maximal among {Wi,K,D} *)
    destruct w; simpl in Hrf; try contradiction.
    unfold L1_abstract_erasure.C4_source. split.
    + unfold L1_abstract_erasure.cand.
      split; [ inE0tac | ]. split; [ exact I | ]. split; [ exact I | ].
      left; unfold gmo; simpl; lia.
    + intros w' Hc'. unfold L1_abstract_erasure.cand in Hc'.
      destruct Hc' as [Hin' [Ww' [Tw' _]]].
      destruct w'; simpl in Ww'; try contradiction.
      * right; unfold gmo; simpl; lia.
      * right; unfold gmo; simpl; lia.
      * left; reflexivity.
Qed.

Lemma h_rftouch : forall w b r, rf w b r -> touches w b.
Proof. intros w b r Hrf. destruct w; simpl in Hrf; try contradiction; exact I. Qed.

Lemma h_rwdisj : forall e, is_read e -> is_write e -> False.
Proof. intros e Hr Hw. destruct e; simpl in Hr, Hw; contradiction. Qed.

Lemma h_hartdk : hart D = hart K.  Proof. reflexivity. Qed.

Lemma h_Hadj : forall b, touches D b ->
  touches D b /\ touches K b /\
  (forall w, In w E0 -> is_write w -> touches w b -> ~ (gmo K w /\ gmo w D)).
Proof.
  intros b _. split; [ exact I | ]. split; [ exact I | ].
  intros w Hin Hw Tw [G1 G2]. unfold gmo in G1, G2.
  destruct w; simpl in Hw; try contradiction; simpl in G1, G2; lia.
Qed.

Lemma h_footdk : forall x, touches D x -> touches K x.
Proof. intros x _; exact I. Qed.

Lemma h_rffun : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.
Proof.
  intros w1 w2 x r H1 H2.
  destruct r; simpl in H1, H2; try contradiction;
  destruct w1; simpl in H1; try contradiction;
  destruct w2; simpl in H2; try contradiction; reflexivity.
Qed.

Lemma h_potrans : forall a b c, po a b -> po b c -> po a c.
Proof. intros a b c H1 H2. unfold po in *. lia. Qed.

Lemma h_pkd : po K D.  Proof. unfold po; simpl; lia. Qed.

Lemma h_pototb : forall e, e <> K -> po e D -> po e K \/ po K e.
Proof.
  intros e Hne Hpo. unfold po in *.
  destruct e; simpl in *; try lia; exfalso; apply Hne; reflexivity.
Qed.

Lemma h_frnit : forall a x, is_read a -> touches a x -> touches D x -> ~ (po K a /\ po a D).
Proof.
  intros a x Hr _ _ [G1 G2]. unfold po in *.
  destruct a; simpl in Hr; try contradiction; simpl in G1, G2; lia.
Qed.

Lemma h_ssd : forall e, (addr e K -> addr e D) /\ (data e K -> data e D).
Proof. intros e. split; intros H; destruct H. Qed.

Lemma h_readerafter : forall bb b, po K b -> rf D bb b -> po D b.
Proof.
  intros bb b _ Hrf. destruct b; simpl in Hrf; try contradiction; unfold po; simpl; lia.
Qed.

(* ============================ apply the capstone ============================ *)

Definition cg2_concrete_instance :=
  frozen_T1_refinement_instantiated
    Ev ev_eq_dec unit unit nat gmo is_write is_read is_read is_write
    touches wval same_addr addr data ctrl fence hart E0 rf po poloc
    K D K D
    h_Hirr h_Htr h_Htot h_din h_dw h_kin h_kw h_kdne h_keeper h_pin h_qin
    h_Hdup h_Hro h_Hdpq h_Hgamma h_dupval h_rfC4 h_rftouch h_rwdisj h_hartdk
    h_Hadj h_footdk h_rffun h_potrans h_pkd h_pototb h_frnit h_ssd h_readerafter
    Hcf Hfrf.

(* cg2_concrete_instance : exists E_N rf_N, <the capstone conclusion, instantiated at this model>. *)

(* ============================ Stage-2 (WIT-1): observation equality ============================ *)
(* The no-fault contraction reproduces the fault run's OBSERVABLE state, EXTRACTED from the proven
   capstone instance (no fresh model needed — the capstone conclusion already carries both halves):
     (a) FINAL MEMORY: the fault co-max write at the lane byte is D (value 7); a SURVIVOR co-max of
         EQUAL value exists after contraction (it is the keeper K, also value 7).
     (b) READ VALUE: the replay read Rs (which read the deleted D, value 7) gets a retargeted source
         of equal value under rf_retarget (the keeper K, value 7).
   So the lane-3 final value and Rs's returned value are both preserved: X_N' observation = X_F. *)

Theorem cg2_stage2_observation :
  (exists w_n,
     Obs_final_state.co_max_of Ev unit gmo is_write touches
       (Obs_final_state.survivor Ev E0 D) tt w_n /\ wval D tt = wval w_n tt)
  /\ (exists w',
     L1_abstract_erasure.rf_retarget Ev unit D K rf w' tt Rs /\ wval w' tt = wval D tt).
Proof.
  destruct cg2_concrete_instance as
    [E_N [rf_N [HE_N [Hrf_N [_ [_ [_ [Hread Hcomax]]]]]]]].
  split.
  - (* final-memory value preserved: feed the concrete fault co-max (w_f = D) *)
    refine (Hcomax tt D _).
    unfold Obs_final_state.co_max_of.
    split; [ exact I | ]. split; [ exact I | ]. split; [ red; inE0tac | ].
    intros w' Hin' Ww' Tw'.
    destruct w'; simpl in Ww'; try contradiction;
      [ right; unfold gmo; simpl; lia
      | right; unfold gmo; simpl; lia
      | left; reflexivity ].
  - (* replay-read value preserved: Rs survives and is retargeted to the equal-valued keeper *)
    assert (HRs_in : In Rs E_N).
    { rewrite HE_N. apply L1_abstract_erasure.In_contract; [ inE0tac | discriminate ]. }
    destruct (Hread Rs tt D HRs_in I I) as [w' [Hrfn Hval]].
    exists w'. rewrite Hrf_N in Hrfn. split; [ exact Hrfn | exact Hval ].
Qed.

