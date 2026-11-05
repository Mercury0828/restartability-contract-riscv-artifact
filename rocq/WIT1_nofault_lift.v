(* WIT1_nofault_lift.v — RESTART-V M4: the WIT-1 full no-fault lift (Stage 2).

   THE GAP THIS CLOSES. `CG2_concrete_instance.v` applies the capstone to a concrete 7-event fault
   execution and obtains the contraction `contract_carrier D`. But that carrier deletes ONLY the
   replay store `D`: it still contains the M-mode trap-region events `Tr`/`Xr`, so it is NOT a
   trap-free no-fault execution. The full "∀ fault run, ∃ no-fault EXECUTION with equal observation"
   headline therefore needs a SEPARATE execution `X_N'` living in the no-fault candidate class whose
   memory projection equals the fault run's. This file builds exactly that, for the same concrete
   VL=4, K=2, P={3} lane-3 single-byte slice.

   WHAT IS PROVED (all 0-axiom, over the CG2 model, reusing its Ev/rank/po/gmo/rf/... unchanged):
     - `EN' = [Wi; Rp; K; Rs]` is genuinely TRAP-FREE: no `Tr`/`Xr` context events and no replay
       duplicate `D`; every event is drawn from the fault run's universe `E0`  (`EN'_is_Cand_N`).
     - `X_N'` is RVWMO-consistent on BOTH frozen checks: the per-location relation `CfN'` and the
       main-model relation `FRfN'` are acyclic (`XN'_perloc_acyclic`, `XN'_mainmodel_acyclic`),
       by the same single rank measure used in CG2.
     - `X_N'`'s reads-from IS the contraction's retargeted reads-from restricted to its carrier:
       `rf_N' w b r <-> rf_retarget D K rf w b r` for every `r` in `EN'`  (`rf_N'_is_retarget`).
       So X_N' is not an ad-hoc execution — it is the erasure's own witness, made trap-free.
     - The MEMORY PROJECTION agrees with the fault run: the coherence-latest write to the lane byte
       is `D` (value 7) in the fault run and `K` (value 7) in X_N', with equal value
       (`wit1_final_memory`); and every read retained in `EN'` gets an X_N' source of equal value
       (`wit1_read_values`) — Rp still reads 0 from Wi, Rs reads 7 from the keeper K instead of 7
       from the deleted replay D.
     - `wit1_nofault_lift` conjoins all of the above.

   HONEST LIMITS (this framing matters more than the result).
     (1) `Cand_N` below formalizes the DEFINING STRUCTURAL FEATURES of the no-fault candidate class
         — no trap/handler/xret events, no replay-phase duplicate, events drawn from the fault
         universe. It is NOT a re-derivation of the full D-a `Cand_N` with all of its state-machine /
         `StateWF` obligations. Those obligations live in the D-a operational layer, which is not
         mechanized here; a claim that X_N' satisfies THEM is not made.
     (2) This is ONE CONCRETE INSTANCE (VL=4, K=2, P={3}, single duplicated lane-3 byte, Byte = unit,
         single hart). It is a non-vacuity / existence certificate for the Stage-2 lift, NOT a
         general ∀-fault-execution lift theorem.
     (3) "Memory projection equality" here = coherence-latest-write value at the byte + every
         retained read's returned value. It is not a concrete memory-array semantics.

   0 Admitted / 0 axioms (Print Assumptions wit1_nofault_lift -> Closed under the global context).
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
Require Import RestartV.CG2_concrete_instance.
Import ListNotations.

(* ===================== the trap-free no-fault carrier X_N' ===================== *)
(* drop the replay store D **and** the whole trap region Tr,Xr. What remains is the plain
   no-fault program order: initial write, prefix read, the single lane store, suffix read. *)

Definition EN' : list Ev := [Wi; Rp; K; Rs].

Definition is_ctx    (e : Ev) : Prop := match e with Tr | Xr => True | _ => False end.
Definition is_replay (e : Ev) : Prop := match e with D => True | _ => False end.

(* Cand_N: the DEFINING STRUCTURAL FEATURES of a no-fault candidate (see HONEST LIMITS (1)). *)
Definition Cand_N (E : list Ev) : Prop :=
  (forall e, In e E -> ~ is_ctx e) /\
  (forall e, In e E -> ~ is_replay e) /\
  (forall e, In e E -> In e E0).

(* the no-fault reads-from: the prefix read takes the initial write, the suffix read takes the
   SINGLE surviving store K (there is no replay to read from any more). *)
Definition rf_N' (w : Ev) (_ : unit) (r : Ev) : Prop :=
  (w = Wi /\ r = Rp) \/ (w = K /\ r = Rs).

Definition CfN' :=
  Clift_coherence.Cf Ev unit gmo is_write is_read touches EN' rf_N' poloc.

Definition FRfN' :=
  Frozen_mainmodel.FRf Ev unit unit gmo is_write is_read is_read is_write
    touches same_addr addr data ctrl fence hart EN' rf_N' po.

(* discharge `In D EN'` / `In Tr EN'` / ... — the events X_N' does NOT contain. *)
Ltac notEN H :=
  simpl in H; repeat (destruct H as [H|H]; [ discriminate H | ]); exact H.

(* ===================== 1. X_N' is a trap-free no-fault candidate ===================== *)

Theorem EN'_is_Cand_N : Cand_N EN'.
Proof.
  unfold Cand_N, EN'. repeat split.
  - intros e H; simpl in H.
    destruct H as [<-|[<-|[<-|[<-|[]]]]]; simpl; exact (fun x => x).
  - intros e H; simpl in H.
    destruct H as [<-|[<-|[<-|[<-|[]]]]]; simpl; exact (fun x => x).
  - intros e H; simpl in H.
    destruct H as [<-|[<-|[<-|[<-|[]]]]]; inE0tac.
Qed.

(* ===================== 2. the bridge: rf_N' IS the retargeted rf on EN' ===================== *)
(* rf_retarget D K rf w b r  =  (rf w b r /\ ~ rf D b r) \/ (rf D b r /\ w = K).
     r = Rp : rf D Rp = False  ==>  RHS = rf w Rp = (w = Wi)          = LHS
     r = Rs : rf D Rs = True   ==>  RHS = (w = K)                     = LHS
     r = Wi / K (writes, never rf-targets): both sides False. *)

Theorem rf_N'_is_retarget : forall w b r,
  In r EN' ->
  (rf_N' w b r <-> L1_abstract_erasure.rf_retarget Ev unit D K rf w b r).
Proof.
  intros w b r _. unfold rf_N', L1_abstract_erasure.rf_retarget.
  destruct r; destruct w; simpl; intuition congruence.
Qed.

(* ===================== 3. both acyclicity checks, by the CG2 rank measure ===================== *)

(* the fr-edge sub-argument, restated for rf_N' (CG2's fr_rank_lemma is stated for rf).
   rf_N' forces (w1,x) in {(Wi,Rp),(K,Rs)}:
     (Wi,Rp): gmo Wi y ==> rank y > 0; y a write of EN' ==> y = K (rank 2); rank Rp = 1 < 2.
     (K ,Rs): gmo K  y ==> rank y > 2; y a write of EN' ==> y in {Wi(0),K(2)} ==> VACUOUS.
   The `In y EN'` premise is exactly co_flt's `inE0` field at this instantiation, and it is
   LOAD-BEARING: without it y = D (rank 5) would satisfy gmo K y yet rank Rs = 6 > 5. *)
Lemma fr_rank_N' : forall (w1 x y : Ev) (b : unit),
  rf_N' w1 b x -> In y EN' -> is_write y -> gmo w1 y -> rank x < rank y.
Proof.
  intros w1 x y b Hrf Hin Hw Hg. unfold gmo in Hg. unfold rf_N' in Hrf.
  destruct Hrf as [[E1 E2] | [E1 E2]]; subst;
  destruct y; simpl in Hw, Hg |- *; try contradiction; try lia;
  exfalso; notEN Hin.
Qed.

(* ppoF over rf_N': only fr1 (po a b) is non-vacuous; fence/addr/data/ctrl are all empty here. *)
Lemma ppoF_rank_N' : forall x y,
  PPO_union.ppoF Ev unit po is_read is_write same_addr addr data ctrl fence rf_N' x y ->
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

Lemma edge_CfN' : forall x y, CfN' x y -> rank x < rank y.
Proof.
  intros x y H. unfold CfN', Clift_coherence.Cf in H.
  destruct H as [ [b Hco] | [ [b [Hrx Hfr]] | [ [b Hrf] | Hpl ] ] ].
  - unfold Clift_coherence.co_flt, Clift_coherence.coOn, Clift_coherence.inE0 in Hco.
    destruct Hco as [_ [_ [_ [_ [_ [_ G]]]]]]. unfold gmo in G; exact G.
  - unfold Clift_coherence.fr_flt in Hfr. destruct Hfr as [w1 [Hrf Hco]].
    unfold Clift_coherence.co_flt, Clift_coherence.coOn, Clift_coherence.inE0 in Hco.
    destruct Hco as [_ [Iny [_ [Wy [_ [_ G]]]]]].
    exact (fr_rank_N' w1 x y b Hrf Iny Wy G).
  - unfold rf_N' in Hrf. destruct Hrf as [[E1 E2] | [E1 E2]]; subst; simpl; lia.
  - unfold poloc in Hpl. destruct Hpl as [Hpo _]. unfold po in Hpo; exact Hpo.
Qed.

Lemma edge_FRfN' : forall x y, FRfN' x y -> rank x < rank y.
Proof.
  intros x y H. unfold FRfN', Frozen_mainmodel.FRf, Rlift_mainmodel.Rf in H.
  destruct H as [ [b Hco] | [ [b [Hrx Hfr]] | [ Hrfe | Hppo ] ] ].
  - unfold Rlift_mainmodel.co_flt, Rlift_mainmodel.coOn, Rlift_mainmodel.inE0 in Hco.
    destruct Hco as [_ [_ [_ [_ [_ [_ G]]]]]]. unfold gmo in G; exact G.
  - unfold Rlift_mainmodel.fr_flt in Hfr. destruct Hfr as [w1 [Hrf Hco]].
    unfold Rlift_mainmodel.co_flt, Rlift_mainmodel.coOn, Rlift_mainmodel.inE0 in Hco.
    destruct Hco as [_ [Iny [_ [Wy [_ [_ G]]]]]].
    exact (fr_rank_N' w1 x y b Hrf Iny Wy G).
  - (* rfe is empty: a single hart, so hart x = hart y = tt always *)
    unfold Rlift_mainmodel.rfe_flt in Hrfe. destruct Hrfe as [b [_ Hne]].
    exfalso; apply Hne; reflexivity.
  - unfold Frozen_mainmodel.fault_ppo in Hppo. destruct Hppo as [Hpf | [bx Hr2]].
    + exact (ppoF_rank_N' x y Hpf).
    + unfold PPO_union.r2F, PPO_union.polnw_F in Hr2.
      destruct Hr2 as [[_ [_ [_ [_ [Hpo _]]]]] _]. unfold po in Hpo; exact Hpo.
Qed.

Theorem XN'_perloc_acyclic : forall x, ~ clos_trans Ev CfN' x x.
Proof. exact (acyc_from_rank CfN' edge_CfN'). Qed.

Theorem XN'_mainmodel_acyclic : forall x, ~ clos_trans Ev FRfN' x x.
Proof. exact (acyc_from_rank FRfN' edge_FRfN'). Qed.

(* ===================== 4. final memory: same coherence-latest value ===================== *)
(* fault run: writes to the lane byte are Wi(0), K(7), D(7); gmo-max is D (rank 5).
   X_N'    : writes are Wi(0), K(7); gmo-max is K (rank 2). wval D = 7 = wval K. *)

(* fault run: the writes to the lane byte are Wi(0), K(2), D(5) in gmo; D is the maximum. *)
Lemma comax_E0_D :
  Obs_final_state.co_max_of Ev unit gmo is_write touches (fun e => In e E0) tt D.
Proof.
  unfold Obs_final_state.co_max_of.
  split; [ exact I | ]. split; [ exact I | ]. split; [ inE0tac | ].
  intros w' Hin' Ww' Tw'.
  destruct w'; simpl in Ww'; try contradiction;
    [ right; unfold gmo; simpl; lia
    | right; unfold gmo; simpl; lia
    | left; reflexivity ].
Qed.

(* X_N': the writes are Wi(0) and K(2) only; K is the maximum. D is absent — this is exactly where
   replay-freeness of the carrier does the work. *)
Lemma comax_EN'_K :
  Obs_final_state.co_max_of Ev unit gmo is_write touches (fun e => In e EN') tt K.
Proof.
  unfold Obs_final_state.co_max_of.
  split; [ exact I | ]. split; [ exact I | ].
  split; [ simpl; right; right; left; reflexivity | ].
  intros w' Hin' Ww' Tw'.
  destruct w'; simpl in Ww'; try contradiction.
  - right; unfold gmo; simpl; lia.
  - left; reflexivity.
  - exfalso; notEN Hin'.
Qed.

Theorem wit1_final_memory :
  Obs_final_state.co_max_of Ev unit gmo is_write touches (fun e => In e E0)  tt D /\
  Obs_final_state.co_max_of Ev unit gmo is_write touches (fun e => In e EN') tt K /\
  wval D tt = wval K tt.
Proof.
  split; [ exact comax_E0_D | ]. split; [ exact comax_EN'_K | ]. reflexivity.
Qed.

(* ===================== 5. read values: every retained read keeps its value ===================== *)

Theorem wit1_read_values : forall r b w,
  In r EN' -> is_read r -> rf w b r ->
  exists w', rf_N' w' b r /\ wval w' b = wval w b.
Proof.
  intros r b w Hin Hr Hrf.
  destruct r; simpl in Hr; try contradiction.
  - (* r = Rp : source is Wi in both runs *)
    destruct w; simpl in Hrf; try contradiction.
    exists Wi. split; [ left; split; reflexivity | reflexivity ].
  - (* r = Rs : source retargeted from the deleted replay D to the keeper K, both value 7 *)
    destruct w; simpl in Hrf; try contradiction.
    exists K. split; [ right; split; reflexivity | reflexivity ].
Qed.

(* ===================== the WIT-1 headline ===================== *)

Theorem wit1_nofault_lift :
  Cand_N EN'
  /\ (forall x, ~ clos_trans Ev CfN'  x x)
  /\ (forall x, ~ clos_trans Ev FRfN' x x)
  /\ (forall w b r, In r EN' ->
        (rf_N' w b r <-> L1_abstract_erasure.rf_retarget Ev unit D K rf w b r))
  /\ (Obs_final_state.co_max_of Ev unit gmo is_write touches (fun e => In e E0)  tt D
      /\ Obs_final_state.co_max_of Ev unit gmo is_write touches (fun e => In e EN') tt K
      /\ wval D tt = wval K tt)
  /\ (forall r b w, In r EN' -> is_read r -> rf w b r ->
        exists w', rf_N' w' b r /\ wval w' b = wval w b).
Proof.
  exact (conj EN'_is_Cand_N
        (conj XN'_perloc_acyclic
        (conj XN'_mainmodel_acyclic
        (conj rf_N'_is_retarget
        (conj wit1_final_memory wit1_read_values))))).
Qed.
