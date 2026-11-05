(* ML_stage2.v — RESTART-V: the Stage-2 capstone for ANY finite set of provisionally written lanes.

   `Stage2_endtoend_v2.stage2_endtoend_v2` carries T1's witness from the contracted carrier, through
   erasure of the memory-silent trap region and of the check events, to the normal candidate, for ONE
   duplicate pair. This file is the same capstone with the one-pair Stage 1 replaced by the
   general-lane theorem `ML_T1.ML_T1_refinement`:

       E0 --(erase every replay duplicate of LS)--> E_C --(erase trap region)--> E_K
          --(erase check events)--> E_MK --(relabel, generate checks)--> E_N

   Everything after Stage 1 is carrier-parametric and is REUSED, not re-proved: the generic §A–§C of
   Stage2_endtoend_v2 (CnC / RnC, memory-silent erasure, NKeep reflection and injection), Ctx_erasure,
   Stage2_normal_candidate, Stage2_obligations and Frozen_pmp. The transported relations are
   ML_T1's own `Cn_L` / `Rn_L` (identified pointwise in the headline), and their acyclicity is
   derived from the FAULT run's antecedents, which are the one-lane capstone's antecedents verbatim.

   WHAT IS NOT CARRIED (unchanged from Stage2_endtoend_v2; read its header):
   E_N is a member of the structural `Cand_N_struct`, not of the operational `Cand_N`; `StateWF` is not
   established (O1 is the interface boundary); O2 is closed against the MODELLED PMP matcher of
   Frozen_pmp, not the ratified `pmpCheck`; `Hctx_silent` / `Hchk_nonmem` are named antecedents.

   0 Admitted / 0 axioms (Print Assumptions ML_stage2_endtoend). No existing .v file is modified.
   Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.PeanoNat.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Rlift_mainmodel.
Require Import RestartV.Frozen_mainmodel.
Require Import RestartV.Obs_final_state.
Require Import RestartV.Ctx_erasure.
Require Import RestartV.Stage2_normal_candidate.
Require Import RestartV.Stage2_obligations.
Require Import RestartV.Frozen_pmp.
Require Import RestartV.Stage2_endtoend_v2.
Require Import RestartV.ML_base.
Require Import RestartV.ML_T1.
Import ListNotations.

Section MLStage2.

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte Hart Value Lane : Type.
  Variable gmo : Event -> Event -> Prop.
  Variable is_write is_read is_load is_store : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable wval : Event -> Byte -> Value.
  Variable same_addr addr data ctrl fence : Event -> Event -> Prop.
  Variable hart : Event -> Hart.
  Variable E0 : list Event.                   (* the FAULT run's carrier *)
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable po poloc : Event -> Event -> Prop.
  Variable LS : list (Event * Event).         (* (keeper, deleted), one pair per provisional lane *)
  Variable Ctx : Event -> Prop.               (* the trap region *)
  Variable ctx_dec : forall e, {Ctx e} + {~ Ctx e}.
  Variable is_chk : Event -> Prop.            (* the fault run's PMP check events *)
  Variable chk_dec : forall e, {is_chk e} + {~ is_chk e}.
  Variable lane : Event -> Lane.
  Variable is_lane_write : Event -> Prop.
  Variable lanes : list Lane.

  (* ---- Stage 1: the general-lane theorem's premises ---- *)
  Hypothesis Hirr : forall e, In e E0 -> ~ gmo e e.
  Hypothesis Htr : forall a b c, In a E0 -> In b E0 -> In c E0 -> gmo a b -> gmo b c -> gmo a c.
  Hypothesis Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.
  Hypothesis Hpo_trans : forall a b c, po a b -> po b c -> po a c.
  Hypothesis Hrf_is_C4 :
    forall b r w, is_read r -> In r E0 -> rf w b r ->
      L1_abstract_erasure.C4_source Event Byte is_write touches gmo po E0 b r w.
  Hypothesis Hrf_touches : forall w b r, rf w b r -> touches w b.
  Hypothesis Hrf_functional : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.
  Hypothesis Hlanes : forall k d, In (k, d) LS ->
    ML_T1.LaneOK Event Byte Hart Value gmo is_write is_read touches wval addr data hart E0 rf po k d.
  Hypothesis Hkeeper_survives : forall k d, In (k, d) LS -> ~ ML_base.isdel Event LS k.

  (* ---- THE TWO CONSISTENCY ANTECEDENTS: the FAULT run's, at the FAULT carrier E0 ---- *)
  Hypothesis Hfault_perloc :
    forall x, ~ clos_trans Event
      (Clift_coherence.Cf Event Byte gmo is_write is_read touches E0 rf poloc) x x.
  Hypothesis Hfault_main :
    forall x, ~ clos_trans Event
      (Frozen_mainmodel.FRf Event Byte Hart gmo is_write is_read is_load is_store touches
         same_addr addr data ctrl fence hart E0 rf po) x x.

  (* ---- RVWMO typing facts (the three `Ctx_erasure` needs) ---- *)
  Hypothesis Hrf_src_write : forall w b r, rf w b r -> is_write w.
  Hypothesis Hrf_tgt_read : forall w b r, rf w b r -> is_read r.
  Hypothesis Hpoloc_touches : forall x y, poloc x y -> exists b, touches x b /\ touches y b.

  (* ---- the two SILENCE antecedents (consequences of the handler schema; not proved here) ---- *)
  Hypothesis Hctx_silent :
    forall e, Ctx e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b).
  Hypothesis Hchk_nonmem :
    forall e, is_chk e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b).

  (* ================================================================================================
     THE CARRIER CHAIN
     ================================================================================================ *)

  Definition E_C : list Event := ML_base.carrier_L Event eq_ev_dec E0 LS.
  Definition rf_C : Event -> Byte -> Event -> Prop := ML_base.rf_L Event LS Byte rf.
  Definition E_K : list Event := Ctx_erasure.EK Event E_C Ctx ctx_dec.
  Definition E_MK : list Event := Stage2_normal_candidate.mem_kernel Event E_K is_chk chk_dec.
  Definition E_N : list (Stage2_normal_candidate.NEv Event Lane) :=
    Stage2_normal_candidate.EN' Event Lane E_K is_chk chk_dec lanes.

  Definition ppow_C : Event -> Event -> Prop :=
    ML_T1.ppo_wit_L Event Byte is_write is_read is_load is_store touches same_addr addr data ctrl
      fence E0 rf po LS.

  Definition survC : Event -> Prop := ML_base.survivor_L Event E0 LS.

  Lemma ppow_C_endpoints : forall x y, ppow_C x y -> survC x /\ survC y.
  Proof.
    intros x y H. unfold ppow_C in H. destruct H; try (split; assumption).
    destruct H as [[_ [_ [_ [_ [_ [Sa [Sb _]]]]]]] _]. split; assumption.
  Qed.

  Definition Cn_C := CnC Event Byte gmo poloc is_read is_write touches rf_C (fun e => In e E_C).
  Definition Cn_K := CnC Event Byte gmo poloc is_read is_write touches rf_C (fun e => In e E_K).
  Definition Cn_MK := CnC Event Byte gmo poloc is_read is_write touches rf_C (fun e => In e E_MK).
  Definition Rn_C := RnC Event Byte Hart gmo is_read is_write touches hart rf_C ppow_C
                         (fun e => In e E_C).
  Definition Rn_K := RnC Event Byte Hart gmo is_read is_write touches hart rf_C ppow_C
                         (fun e => In e E_K).
  Definition Rn_MK := RnC Event Byte Hart gmo is_read is_write touches hart rf_C ppow_C
                          (fun e => In e E_MK).

  Definition Cn_N :=
    CnC (Stage2_normal_candidate.NEv Event Lane) Byte
      (Stage2_normal_candidate.gmo_N Event Lane gmo)
      (Stage2_normal_candidate.poloc_N Event Lane poloc)
      (Stage2_normal_candidate.is_read_N Event Lane is_read)
      (Stage2_normal_candidate.is_write_N Event Lane is_write)
      (Stage2_normal_candidate.touches_N Event Byte Lane touches)
      (Stage2_normal_candidate.rf_N Event Byte Lane rf_C)
      (fun z => In z E_N).

  Definition Rn_N :=
    RnC (Stage2_normal_candidate.NEv Event Lane) Byte (option Hart)
      (Stage2_normal_candidate.gmo_N Event Lane gmo)
      (Stage2_normal_candidate.is_read_N Event Lane is_read)
      (Stage2_normal_candidate.is_write_N Event Lane is_write)
      (Stage2_normal_candidate.touches_N Event Byte Lane touches)
      (hart_N Event Hart Lane hart)
      (Stage2_normal_candidate.rf_N Event Byte Lane rf_C)
      (ppo_N Event Lane ppow_C)
      (fun z => In z E_N).

  (* ================================================================================================
     STAGE 1 IS THE GENERAL-LANE THEOREM, APPLIED
     ================================================================================================ *)

  Definition T1_OUT :=
    ML_T1.ML_T1_refinement
      Event eq_ev_dec Byte Hart Value gmo is_write is_read is_load is_store touches wval
      same_addr addr data ctrl fence hart E0 rf po poloc LS
      Hirr Htr Htot Hpo_trans Hrf_is_C4 Hrf_touches Hrf_functional Hlanes Hkeeper_survives
      Hfault_perloc Hfault_main.

  Lemma in_EC_surv : forall e, In e E_C -> survC e.
  Proof. intros e H. exact (proj1 (ML_base.survivor_carrier Event eq_ev_dec E0 LS e) H). Qed.

  Lemma surv_in_EC : forall e, survC e -> In e E_C.
  Proof. intros e H. exact (proj2 (ML_base.survivor_carrier Event eq_ev_dec E0 LS e) H). Qed.

  (* the transported relations ARE ML_T1's own Cn_L / Rn_L, pointwise *)
  Theorem Cn_C_is_ML_Cn : forall x y,
    Cn_C x y <-> ML_T1.Cn_L Event Byte gmo is_write is_read touches E0 rf poloc LS x y.
  Proof.
    intros x y. split; intro H.
    - exact (CnC_mono Event Byte gmo poloc is_read is_write touches rf_C survC (fun e => In e E_C)
               in_EC_surv x y H).
    - exact (CnC_mono Event Byte gmo poloc is_read is_write touches rf_C (fun e => In e E_C) survC
               surv_in_EC x y H).
  Qed.

  Theorem Rn_C_is_ML_Rn : forall x y,
    Rn_C x y <->
    ML_T1.Rn_L Event Byte Hart gmo is_write is_read is_load is_store touches same_addr addr data
      ctrl fence hart E0 rf po LS x y.
  Proof.
    intros x y. split; intro H.
    - pose proof (RnC_mono Event Byte Hart gmo is_read is_write touches hart rf_C ppow_C
                    survC (fun e => In e E_C) in_EC_surv x y H) as H'.
      destruct H' as [Hco | [Hfr | [Hrfe | [_ [_ Hpp]]]]].
      + left; exact Hco.
      + right; left; exact Hfr.
      + right; right; left; exact Hrfe.
      + right; right; right; exact Hpp.
    - apply (RnC_mono Event Byte Hart gmo is_read is_write touches hart rf_C ppow_C
               (fun e => In e E_C) survC surv_in_EC x y).
      destruct H as [Hco | [Hfr | [Hrfe | Hpp]]].
      + left; exact Hco.
      + right; left; exact Hfr.
      + right; right; left; exact Hrfe.
      + right; right; right. destruct (ppow_C_endpoints x y Hpp) as [Sx Sy].
        split; [exact Sx |]. split; [exact Sy | exact Hpp].
  Qed.

  Lemma Cn_C_acyclic : forall x, ~ clos_trans Event Cn_C x x.
  Proof.
    destruct T1_OUT as [EN [rfN [_ [_ [Hcn [_ [_ [_ _]]]]]]]].
    apply (acyclic_sub Event (ML_T1.Cn_L Event Byte gmo is_write is_read touches E0 rf poloc LS) Cn_C).
    - intros x y H. apply Cn_C_is_ML_Cn. exact H.
    - exact Hcn.
  Qed.

  Lemma Rn_C_acyclic : forall x, ~ clos_trans Event Rn_C x x.
  Proof.
    destruct T1_OUT as [EN [rfN [_ [_ [_ [Hrn [_ [_ _]]]]]]]].
    apply (acyclic_sub Event
             (ML_T1.Rn_L Event Byte Hart gmo is_write is_read is_load is_store touches same_addr addr
                data ctrl fence hart E0 rf po LS) Rn_C).
    - intros x y H. apply Rn_C_is_ML_Rn. exact H.
    - exact Hrn.
  Qed.

  (* ================================================================================================
     THE TWO ERASURE HOPS (generic lemmas of Stage2_endtoend_v2, at this chain)
     ================================================================================================ *)

  Lemma rfC_src_write : forall w b r, rf_C w b r -> is_write w.
  Proof.
    intros w b r H. unfold rf_C, ML_base.rf_L in H.
    destruct H as [[H1 _] | [d [Hl _]]].
    - exact (Hrf_src_write w b r H1).
    - exact (ML_T1.lk_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Hlanes w d Hl)).
  Qed.

  Lemma rfC_tgt_read : forall w b r, rf_C w b r -> is_read r.
  Proof.
    intros w b r H. unfold rf_C, ML_base.rf_L in H.
    destruct H as [[H1 _] | [d [_ H1]]].
    - exact (Hrf_tgt_read w b r H1).
    - exact (Hrf_tgt_read d b r H1).
  Qed.

  Theorem Cn_C_iff_Cn_K : forall x y, Cn_C x y <-> Cn_K x y.
  Proof.
    exact (CnC_erase_iff Event Byte gmo poloc is_read is_write touches rf_C E_C Ctx ctx_dec
             Hctx_silent Hpoloc_touches rfC_src_write rfC_tgt_read).
  Qed.

  Theorem Rn_K_sub_Rn_C : forall x y, Rn_K x y -> Rn_C x y.
  Proof.
    exact (RnC_erase_sub Event Byte Hart gmo is_read is_write touches hart rf_C ppow_C
             E_C Ctx ctx_dec).
  Qed.

  Theorem Cn_K_iff_Cn_MK : forall x y, Cn_K x y <-> Cn_MK x y.
  Proof.
    exact (CnC_erase_iff Event Byte gmo poloc is_read is_write touches rf_C E_K is_chk chk_dec
             Hchk_nonmem Hpoloc_touches rfC_src_write rfC_tgt_read).
  Qed.

  Theorem Rn_MK_sub_Rn_K : forall x y, Rn_MK x y -> Rn_K x y.
  Proof.
    exact (RnC_erase_sub Event Byte Hart gmo is_read is_write touches hart rf_C ppow_C
             E_K is_chk chk_dec).
  Qed.

  Lemma Cn_MK_acyclic : forall x, ~ clos_trans Event Cn_MK x x.
  Proof.
    apply (acyclic_sub Event Cn_C Cn_MK).
    - intros x y H. apply Cn_C_iff_Cn_K. apply Cn_K_iff_Cn_MK. exact H.
    - exact Cn_C_acyclic.
  Qed.

  Lemma Rn_MK_acyclic : forall x, ~ clos_trans Event Rn_MK x x.
  Proof.
    apply (acyclic_sub Event Rn_C Rn_MK).
    - intros x y H. apply Rn_K_sub_Rn_C. apply Rn_MK_sub_Rn_K. exact H.
    - exact Rn_C_acyclic.
  Qed.

  Theorem endtoend_perloc_acyclic :
    forall n, ~ clos_trans (Stage2_normal_candidate.NEv Event Lane) Cn_N n n.
  Proof.
    exact (CnN_acyclic Event Byte Lane gmo poloc is_read is_write touches rf_C
             E_K is_chk chk_dec lanes Cn_MK_acyclic).
  Qed.

  Theorem endtoend_mainmodel_acyclic :
    forall n, ~ clos_trans (Stage2_normal_candidate.NEv Event Lane) Rn_N n n.
  Proof.
    exact (RnN_acyclic Event Byte Hart Lane gmo is_read is_write touches hart rf_C ppow_C
             E_K is_chk chk_dec lanes Rn_MK_acyclic).
  Qed.

  Theorem Cn_N_is_Cn_MK : forall a b,
    Cn_N (Stage2_normal_candidate.NKeep Event Lane a) (Stage2_normal_candidate.NKeep Event Lane b)
    <-> Cn_MK a b.
  Proof.
    intros a b. split.
    - intro H.
      destruct (CnN_reflect Event Byte Lane gmo poloc is_read is_write touches rf_C
                  E_K is_chk chk_dec lanes _ _ H) as [a' [b' [Ha [Hb Hc]]]].
      injection Ha as Ha. injection Hb as Hb. subst a' b'. exact Hc.
    - intro H.
      exact (CnN_inject Event Byte Lane gmo poloc is_read is_write touches rf_C
               E_K is_chk chk_dec lanes a b H).
  Qed.

  Theorem Rn_N_is_Rn_MK : forall a b,
    Rn_N (Stage2_normal_candidate.NKeep Event Lane a) (Stage2_normal_candidate.NKeep Event Lane b)
    <-> Rn_MK a b.
  Proof.
    intros a b. split.
    - intro H.
      destruct (RnN_reflect Event Byte Hart Lane gmo is_read is_write touches hart rf_C ppow_C
                  E_K is_chk chk_dec lanes _ _ H) as [a' [b' [Ha [Hb Hc]]]].
      injection Ha as Ha. injection Hb as Hb. subst a' b'. exact Hc.
    - intro H.
      exact (RnN_inject Event Byte Hart Lane gmo is_read is_write touches hart rf_C ppow_C
               E_K is_chk chk_dec lanes a b H).
  Qed.

  (* ================================================================================================
     THE CARRIERS NEST
     ================================================================================================ *)

  Lemma E_C_sub_E0 : forall e, In e E_C -> In e E0.
  Proof. exact (ML_base.carrier_sub Event eq_ev_dec E0 LS). Qed.

  Lemma E_K_sub_E_C : forall e, In e E_K -> In e E_C.
  Proof. exact (Ctx_erasure.EK_sub Event E_C Ctx ctx_dec). Qed.

  Lemma E_MK_sub_E_K : forall e, In e E_MK -> In e E_K.
  Proof. exact (Stage2_normal_candidate.mem_kernel_sub Event E_K is_chk chk_dec). Qed.

  Lemma E_N_NKeep_iff :
    forall e, In (Stage2_normal_candidate.NKeep Event Lane e) E_N <-> In e E_MK.
  Proof.
    intro e. split.
    - exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane E_K is_chk chk_dec lanes e).
    - exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane E_K is_chk chk_dec lanes e).
  Qed.

  Lemma E_K_trap_free : forall e, In e E_K -> ~ Ctx e.
  Proof. exact (Ctx_erasure.EK_trap_free Event E_C Ctx ctx_dec). Qed.

  Lemma E_C_no_replay : forall k d, In (k, d) LS -> ~ In d E_C.
  Proof.
    intros k d Hl H. apply in_EC_surv in H. destruct H as [_ H].
    apply H. exact (ML_base.lane_del Event LS k d Hl).
  Qed.

  (* ================================================================================================
     STAGE 1's OBSERVATION HALF, carried through
     ================================================================================================ *)

  Lemma endtoend_L1_consistent :
    L1_abstract_erasure.L1_consistent Event Byte is_write is_read touches gmo po E_C rf_C.
  Proof. destruct T1_OUT as [EN [rfN [He [Hr [_ [_ [Hl1 _]]]]]]]. rewrite He, Hr in Hl1. exact Hl1. Qed.

  Lemma endtoend_read_values :
    forall r b w, In r E_C -> is_read r -> rf w b r ->
      exists w', rf_C w' b r /\ wval w' b = wval w b.
  Proof.
    destruct T1_OUT as [EN [rfN [He [Hr [_ [_ [_ [Hobs _]]]]]]]].
    rewrite He, Hr in Hobs. exact Hobs.
  Qed.

  Lemma endtoend_final_state :
    forall b w_f,
      Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E0) b w_f ->
      exists w_n, Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E_C) b w_n
                  /\ wval w_f b = wval w_n b.
  Proof.
    destruct T1_OUT as [EN [rfN [_ [_ [_ [_ [_ [_ Hfin]]]]]]]].
    intros b w_f H.
    destruct (Hfin b w_f H) as [w_n [Hmax Hval]].
    exists w_n. split; [| exact Hval].
    apply (co_max_of_ext Event Byte gmo is_write touches survC (fun e => In e E_C)
             (fun e => iff_sym (ML_base.survivor_carrier Event eq_ev_dec E0 LS e)) b w_n Hmax).
  Qed.

  Lemma endtoend_co_max : forall b w,
    Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E_C) b w
    <-> Obs_final_state.co_max_of (Stage2_normal_candidate.NEv Event Lane) Byte
          (Stage2_normal_candidate.gmo_N Event Lane gmo)
          (Stage2_normal_candidate.is_write_N Event Lane is_write)
          (Stage2_normal_candidate.touches_N Event Byte Lane touches)
          (fun n => In n E_N) b (Stage2_normal_candidate.NKeep Event Lane w).
  Proof.
    intros b w.
    pose proof (Ctx_erasure.erase_ctx_preserves_co_max Event Byte gmo is_read is_write touches
                  E_C Ctx ctx_dec Hctx_silent b w) as H1.
    pose proof (Ctx_erasure.erase_ctx_preserves_co_max Event Byte gmo is_read is_write touches
                  E_K is_chk chk_dec Hchk_nonmem b w) as H2.
    pose proof (Stage2_normal_candidate.transport_co_max Event Byte Lane gmo is_write touches
                  E_K is_chk chk_dec lanes b w) as H3.
    split.
    - intro H. apply H3. apply H2. apply H1. exact H.
    - intro H. apply H1. apply H2. apply H3. exact H.
  Qed.

  (* O3 at the wired chain: the normal candidate's reads-from is the kernel's along NKeep *)
  Lemma endtoend_O3 :
    forall r b w, In r E_C -> is_read r -> rf w b r ->
      exists w' : Event,
        Stage2_normal_candidate.rf_N Event Byte Lane rf_C
          (Stage2_normal_candidate.NKeep Event Lane w') b
          (Stage2_normal_candidate.NKeep Event Lane r)
        /\ wval w' b = wval w b.
  Proof.
    intros r b w Hr Hrd Hrf.
    destruct (endtoend_read_values r b w Hr Hrd Hrf) as [w' [Hw' Hv]].
    exists w'. split; [exact Hw' | exact Hv].
  Qed.

  (* ================================================================================================
     O2 AT THE WIRED LANES (Frozen_pmp's modelled matcher, as in Stage2_endtoend_v2)
     ================================================================================================ *)

  Variable dst VL Kl ram_lo ram_hi : nat.
  Variable lane_index : Lane -> nat.
  Variable byte_addr : Byte -> nat.
  Hypothesis HK_lt : Kl < VL.
  Hypothesis Hbg_covers : forall i, i < VL ->
    ram_lo <= Frozen_pmp.lane_lo dst i /\ Frozen_pmp.lane_hi dst i <= ram_hi.
  Hypothesis Hlanes_nonempty : lanes <> nil.
  Hypothesis Hlanes_complete : forall l : Lane, In l lanes.
  Hypothesis Hlanes_in_range : forall l, In l lanes -> lane_index l < VL.
  Hypothesis Hlanes_cover : forall i, i < VL ->
    exists l, In l lanes /\ lane_index l = i.
  Hypothesis Hlane_index_injective : forall l1 l2,
    In l1 lanes -> In l2 lanes -> lane_index l1 = lane_index l2 -> l1 = l2.
  Hypothesis Hlane_write_footprint : forall e l b,
    In e E_K -> is_lane_write e -> lane e = l ->
    (touches e b <->
       Frozen_pmp.lane_lo dst (lane_index l) <= byte_addr b /\
       byte_addr b < Frozen_pmp.lane_hi dst (lane_index l)).

  Definition pmp_grants (e : Frozen_pmp.Entry) (l : Lane) : Prop :=
    Frozen_pmp.allows (e :: Frozen_pmp.entry_background ram_lo ram_hi :: nil)
      (Frozen_pmp.lane_lo dst (lane_index l)) (Frozen_pmp.lane_hi dst (lane_index l))
      Frozen_pmp.PrivU.

  Lemma pmp_ok_grants : forall l, pmp_grants (Frozen_pmp.entry_repaired dst Kl) l.
  Proof.
    intro l.
    exact (Frozen_pmp.frozen_pmp_lane_checks_succeed dst VL Kl HK_lt ram_lo ram_hi Hbg_covers
             (lane_index l) (Hlanes_in_range l (Hlanes_complete l))).
  Qed.

  Lemma endtoend_O2 :
    forall (t : nat -> Frozen_pmp.Entry) (l : Lane),
      Stage2_obligations.check_succeeds nat Frozen_pmp.Entry Lane 0 pmp_grants
        (Stage2_obligations.pmp_repaired nat Frozen_pmp.Entry Nat.eq_dec 0
           (Frozen_pmp.entry_repaired dst Kl) t) l.
  Proof.
    exact (Stage2_obligations.O2_closed nat Frozen_pmp.Entry Lane Nat.eq_dec 0
             (Frozen_pmp.entry_repaired dst Kl) pmp_grants pmp_ok_grants).
  Qed.

  Lemma endtoend_O2_lanes :
    forall l, In l lanes ->
      Frozen_pmp.allows (Frozen_pmp.repaired_table dst Kl ram_lo ram_hi)
        (Frozen_pmp.lane_lo dst (lane_index l)) (Frozen_pmp.lane_hi dst (lane_index l))
        Frozen_pmp.PrivU.
  Proof. intros l _. exact (pmp_ok_grants l). Qed.

  Lemma endtoend_O2_index_wiring :
    lanes <> nil /\
    (forall l : Lane, In l lanes) /\
    (forall i, i < VL -> exists l, In l lanes /\ lane_index l = i) /\
    (forall l1 l2, In l1 lanes -> In l2 lanes ->
       lane_index l1 = lane_index l2 -> l1 = l2).
  Proof.
    split; [exact Hlanes_nonempty|].
    split; [exact Hlanes_complete|].
    split; [exact Hlanes_cover|].
    exact Hlane_index_injective.
  Qed.

  Lemma endtoend_O2_event_wiring :
    forall e l, In e E_K -> is_lane_write e -> lane e = l ->
      (forall b,
         touches e b <->
         Frozen_pmp.lane_lo dst (lane_index l) <= byte_addr b /\
         byte_addr b < Frozen_pmp.lane_hi dst (lane_index l)) /\
      Frozen_pmp.allows (Frozen_pmp.repaired_table dst Kl ram_lo ram_hi)
        (Frozen_pmp.lane_lo dst (lane_index l)) (Frozen_pmp.lane_hi dst (lane_index l))
        Frozen_pmp.PrivU.
  Proof.
    intros e l He Hw Hel. split.
    - intro b. exact (Hlane_write_footprint e l b He Hw Hel).
    - exact (pmp_ok_grants l).
  Qed.

  Hypothesis Hkernel_one_write_per_lane :
    forall l, In l lanes ->
      exists w, In w E_K /\ is_lane_write w /\ lane w = l /\
                (forall w', In w' E_K -> is_lane_write w' -> lane w' = l -> w' = w).
  Hypothesis Hlane_write_is_write : forall e, is_lane_write e -> is_write e.

  Lemma endtoend_Cand_N_struct :
    Stage2_normal_candidate.Cand_N_struct Event Lane E_K lane is_lane_write is_chk chk_dec lanes.
  Proof.
    exact (Stage2_normal_candidate.EN'_Cand_N_struct Event Byte Lane is_read is_write touches E_K
             lane is_lane_write is_chk chk_dec lanes
             Hkernel_one_write_per_lane Hchk_nonmem Hlane_write_is_write).
  Qed.

  (* ================================================================================================
     HEADLINE
     ================================================================================================ *)

  Theorem ML_stage2_endtoend :
    (* --- 1. the carrier chain nests; every replay duplicate of every lane is gone --- *)
    ((forall e, In e E_C -> In e E0)
     /\ (forall k d, In (k, d) LS -> ~ In d E_C)
     /\ (forall e, In e E_K -> In e E_C)
     /\ (forall e, In e E_MK -> In e E_K)
     /\ (forall e, In (Stage2_normal_candidate.NKeep Event Lane e) E_N <-> In e E_MK)
     /\ (forall e, In e E_K -> ~ Ctx e))
    (* --- 2. Stage 1 consumed: C4 and both observation halves at E_C --- *)
    /\ L1_abstract_erasure.L1_consistent Event Byte is_write is_read touches gmo po E_C rf_C
    /\ (forall r b w, In r E_C -> is_read r -> rf w b r ->
          exists w', rf_C w' b r /\ wval w' b = wval w b)
    /\ (forall b w_f,
          Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E0) b w_f ->
          exists w_n,
            Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E_C) b w_n
            /\ wval w_f b = wval w_n b)
    (* --- 3. the transported relations ARE ML_T1's Cn_L / Rn_L, and are acyclic (derived) --- *)
    /\ (forall x y, Cn_C x y <->
          ML_T1.Cn_L Event Byte gmo is_write is_read touches E0 rf poloc LS x y)
    /\ (forall x y, Rn_C x y <->
          ML_T1.Rn_L Event Byte Hart gmo is_write is_read is_load is_store touches same_addr addr
            data ctrl fence hart E0 rf po LS x y)
    /\ (forall x y, ppow_C x y -> survC x /\ survC y)
    /\ (forall x, ~ clos_trans Event Cn_C x x)
    /\ (forall x, ~ clos_trans Event Rn_C x x)
    (* --- 4. the two erasure hops --- *)
    /\ (forall x y, Cn_C x y <-> Cn_K x y)
    /\ (forall x y, Rn_K x y -> Rn_C x y)
    /\ (forall x y, Cn_K x y <-> Cn_MK x y)
    /\ (forall x y, Rn_MK x y -> Rn_K x y)
    (* --- 5. both RVWMO checks arrive at the normal candidate, non-vacuously --- *)
    /\ (forall a b, Cn_N (Stage2_normal_candidate.NKeep Event Lane a)
                         (Stage2_normal_candidate.NKeep Event Lane b) <-> Cn_MK a b)
    /\ (forall a b, Rn_N (Stage2_normal_candidate.NKeep Event Lane a)
                         (Stage2_normal_candidate.NKeep Event Lane b) <-> Rn_MK a b)
    /\ (forall n, ~ clos_trans (Stage2_normal_candidate.NEv Event Lane) Cn_N n n)
    /\ (forall n, ~ clos_trans (Stage2_normal_candidate.NEv Event Lane) Rn_N n n)
    (* --- 6. the byte-wise memory projection along the whole chain --- *)
    /\ (forall b w,
          Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E_C) b w
          <-> Obs_final_state.co_max_of (Stage2_normal_candidate.NEv Event Lane) Byte
                (Stage2_normal_candidate.gmo_N Event Lane gmo)
                (Stage2_normal_candidate.is_write_N Event Lane is_write)
                (Stage2_normal_candidate.touches_N Event Byte Lane touches)
                (fun n => In n E_N) b (Stage2_normal_candidate.NKeep Event Lane w))
    (* --- 7. Layer 3's STRUCTURAL candidate (NOT the operational Cand_N) --- *)
    /\ Stage2_normal_candidate.Cand_N_struct Event Lane E_K lane is_lane_write is_chk chk_dec lanes
    (* --- 8. O3 at the wired chain --- *)
    /\ (forall r b w, In r E_C -> is_read r -> rf w b r ->
          exists w' : Event,
            Stage2_normal_candidate.rf_N Event Byte Lane rf_C
              (Stage2_normal_candidate.NKeep Event Lane w') b
              (Stage2_normal_candidate.NKeep Event Lane r)
            /\ wval w' b = wval w b)
    (* --- 9. O2: lane/index/event wiring, then the modelled PMP conclusions --- *)
    /\ (lanes <> nil
        /\ (forall l : Lane, In l lanes)
        /\ (forall i, i < VL -> exists l, In l lanes /\ lane_index l = i)
        /\ (forall l1 l2, In l1 lanes -> In l2 lanes ->
             lane_index l1 = lane_index l2 -> l1 = l2))
    /\ (forall e l, In e E_K -> is_lane_write e -> lane e = l ->
          (forall b,
             touches e b <->
             Frozen_pmp.lane_lo dst (lane_index l) <= byte_addr b /\
             byte_addr b < Frozen_pmp.lane_hi dst (lane_index l)) /\
          Frozen_pmp.allows (Frozen_pmp.repaired_table dst Kl ram_lo ram_hi)
            (Frozen_pmp.lane_lo dst (lane_index l))
            (Frozen_pmp.lane_hi dst (lane_index l))
            Frozen_pmp.PrivU)
    /\ (forall l, In l lanes ->
          Frozen_pmp.allows (Frozen_pmp.repaired_table dst Kl ram_lo ram_hi)
            (Frozen_pmp.lane_lo dst (lane_index l)) (Frozen_pmp.lane_hi dst (lane_index l))
            Frozen_pmp.PrivU)
    /\ (forall (t : nat -> Frozen_pmp.Entry) (l : Lane),
          Stage2_obligations.check_succeeds nat Frozen_pmp.Entry Lane 0 pmp_grants
            (Stage2_obligations.pmp_repaired nat Frozen_pmp.Entry Nat.eq_dec 0
               (Frozen_pmp.entry_repaired dst Kl) t) l).
  Proof.
    split.
    { split; [exact E_C_sub_E0|].
      split; [exact E_C_no_replay|].
      split; [exact E_K_sub_E_C|].
      split; [exact E_MK_sub_E_K|].
      split; [exact E_N_NKeep_iff | exact E_K_trap_free]. }
    split; [exact endtoend_L1_consistent|].
    split; [exact endtoend_read_values|].
    split; [exact endtoend_final_state|].
    split; [exact Cn_C_is_ML_Cn|].
    split; [exact Rn_C_is_ML_Rn|].
    split; [exact ppow_C_endpoints|].
    split; [exact Cn_C_acyclic|].
    split; [exact Rn_C_acyclic|].
    split; [exact Cn_C_iff_Cn_K|].
    split; [exact Rn_K_sub_Rn_C|].
    split; [exact Cn_K_iff_Cn_MK|].
    split; [exact Rn_MK_sub_Rn_K|].
    split; [exact Cn_N_is_Cn_MK|].
    split; [exact Rn_N_is_Rn_MK|].
    split; [exact endtoend_perloc_acyclic|].
    split; [exact endtoend_mainmodel_acyclic|].
    split; [exact endtoend_co_max|].
    split; [exact endtoend_Cand_N_struct|].
    split; [exact endtoend_O3|].
    split; [exact endtoend_O2_index_wiring|].
    split; [exact endtoend_O2_event_wiring|].
    split; [exact endtoend_O2_lanes | exact endtoend_O2].
  Qed.

End MLStage2.
