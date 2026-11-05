(* T1_consistency.v — RESTART-V M4: the mechanized COMPOSITION of the two witness-lift theorems.

   Round-13 audit GAP C observed that the "layers compose to witness-consistency" claim was only
   NARRATED — no Coq term tied the abstract transfer to Clift_coherence.`Cn_lifts` /
   Rlift_mainmodel.`Rn_lifts`. This file supplies that term: it `Require`s both companion files and,
   under one shared set of model parameters and hypotheses, proves BOTH RVWMO acyclicity checks for
   the constructed witness at once —

       witness_passes_both_checks :
         (fault per-location acyclic) -> (fault main-model acyclic) -> (the ppo-edge lift) ->
         (witness per-location acyclic) /\ (witness main-model acyclic)

   by applying `witness_perloc_acyclic` and `witness_mainmodel_acyclic` to the shared data.

   HONESTY SCOPE (unchanged from round-13). This composes the two acyclicity results into one term,
   but it is STILL not the whole T1: (i) the ppo-edge lift `ppo_lifts` is a hypothesis, not proved
   from concrete PPO r1-r13; (ii) the fault-run's two acyclicity checks are hypotheses (the fault run
   is assumed CONSISTENT); (iii) nothing here proves that Cn/Cf/Rn/Rf are the relations of ONE
   concrete witness produced by L1's `contract_carrier` / `rf_retarget` — they are supplied
   abstractly; (iv) the OBSERVATIONAL half of T1 (the observation projection O, R0, the
   ∀fault∃no-fault matching) is absent. What IS now a theorem: "given the fault run is consistent and
   the ppo edges lift, the constructed witness satisfies both RVWMO consistency checks."
   Self-contained modulo the two companions; 0 Admitted / 0 axioms (Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Rlift_mainmodel.
Import ListNotations.

Section Compose.

  Variables Event Byte Hart : Type.
  Variable gmo : Event -> Event -> Prop.
  Variable is_write is_read : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable hart : Event -> Hart.
  Variable E0 : list Event.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable poloc ppo ppo_wit : Event -> Event -> Prop.
  Variables d k : Event.

  Hypothesis d_in : In d E0.
  Hypothesis d_w  : is_write d.
  Hypothesis k_in : In k E0.
  Hypothesis k_w  : is_write k.
  Hypothesis rf_touches : forall w bb r, rf w bb r -> touches w bb.
  Hypothesis keeper_before : gmo k d.
  Hypothesis hart_dk : hart d = hart k.
  Hypothesis Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.
  (* shared adjacency at d's footprint bytes (unfolds to both companions' `adj`) *)
  Hypothesis Hadj : forall b, touches d b ->
      touches d b /\ touches k b /\
      (forall w, In w E0 -> is_write w -> touches w b -> ~ (gmo k w /\ gmo w d)).

  Theorem witness_passes_both_checks :
    (* fault run is CONSISTENT: both RVWMO acyclicity checks pass on the fault relations *)
    (forall x, ~ clos_trans Event
       (Clift_coherence.Cf Event Byte gmo is_write is_read touches E0 rf poloc) x x) ->
    (forall x, ~ clos_trans Event
       (Rlift_mainmodel.Rf Event Byte Hart gmo is_write is_read touches hart E0 rf ppo) x x) ->
    (* the one remaining edge-kind obligation: witness ppo edges lift to fault paths *)
    (forall x y, ppo_wit x y -> clos_trans Event
       (Rlift_mainmodel.Rf Event Byte Hart gmo is_write is_read touches hart E0 rf ppo) x y) ->
    (* THEN the constructed witness passes both checks *)
    (forall x, ~ clos_trans Event
       (Clift_coherence.Cn Event Byte gmo is_write is_read touches E0 rf poloc d k) x x) /\
    (forall x, ~ clos_trans Event
       (Rlift_mainmodel.Rn Event Byte Hart gmo is_write is_read touches hart E0 rf ppo_wit d k) x x).
  Proof.
    intros Hcf Hrf Hppo. split.
    - exact (witness_perloc_acyclic Event Byte gmo is_write is_read touches E0 rf poloc d k
               d_in d_w k_in k_w rf_touches keeper_before
               (Clift_coherence.Build_gmo_wf Event gmo E0 Htot) Hadj Hcf).
    - exact (witness_mainmodel_acyclic Event Byte Hart gmo is_write is_read touches hart E0 rf
               ppo ppo_wit d k
               d_in d_w k_in k_w rf_touches keeper_before hart_dk
               (Rlift_mainmodel.Build_gmo_wf Event gmo E0 Htot) Hadj Hppo Hrf).
  Qed.

End Compose.
