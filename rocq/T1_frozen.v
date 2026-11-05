(* T1_frozen.v — RESTART-V M4: the frozen witness passes BOTH RVWMO consistency checks, with the
   ppo_lifts premise DISCHARGED. The web-Pro Route-C consistency capstone.

   T1_consistency.`witness_passes_both_checks` composed the two abstract lift theorems but still took
   `ppo_lifts` as a premise. This file replaces that premise with the concrete frozen PPO (via
   Frozen_mainmodel), and combines it with Clift's per-location result, proving:

     given the FAULT run is consistent (both per-location Cf and main-model FRf acyclic) and the
     frozen RO/token modelling hypotheses hold, the constructed witness passes BOTH checks
     (per-location Cn and main-model Rn acyclic) — with NO `ppo_lifts` premise.

   This meets web-Pro stopping-rule item 2 (no ppo_lifts / ppo⊆gmo premise) for the consistency
   half of T1. What remains for the closed ∀∃ T1: package the observation (read-values + final state)
   alongside, exhibit the contracted execution, and quantify ∀X_F ∃X_N. Self-contained modulo Clift +
   Frozen_mainmodel; 0 Admitted / 0 axioms (Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Frozen_mainmodel.
Import ListNotations.

Section T1Frozen.

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte Hart : Type.
  Variable gmo : Event -> Event -> Prop.
  Variable is_write is_read is_load is_store : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable same_addr addr data ctrl fence : Event -> Event -> Prop.
  Variable hart : Event -> Hart.
  Variable E0 : list Event.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable po : Event -> Event -> Prop.
  Variable poloc : Event -> Event -> Prop.
  Variables d k : Event.

  Hypothesis d_in : In d E0.
  Hypothesis d_w  : is_write d.
  Hypothesis k_in : In k E0.
  Hypothesis k_w  : is_write k.
  Hypothesis kd_ne : k <> d.
  Hypothesis rf_touches : forall w bb r, rf w bb r -> touches w bb.
  Hypothesis keeper_before : gmo k d.
  Hypothesis hart_dk : hart d = hart k.
  Hypothesis Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.
  Hypothesis Hadj : forall b, touches d b ->
      touches d b /\ touches k b /\
      (forall w, In w E0 -> is_write w -> touches w b -> ~ (gmo k w /\ gmo w d)).
  Hypothesis foot_dk : forall x, touches d x -> touches k x.
  Hypothesis po_twin : forall a b x,
    is_read a -> touches a x -> touches d x -> po a d -> po d b -> po a k /\ po k b.
  Hypothesis rf_functional : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.
  Hypothesis dup_r12 : forall a b bb,
      po a k -> po k b -> (addr a k \/ data a k) -> rf d bb b ->
      po a d /\ po d b /\ (addr a d \/ data a d).

  Let Cf := Clift_coherence.Cf Event Byte gmo is_write is_read touches E0 rf poloc.
  Let Cn := Clift_coherence.Cn Event Byte gmo is_write is_read touches E0 rf poloc d k.
  Let FRf := Frozen_mainmodel.FRf Event Byte Hart gmo is_write is_read is_load is_store touches
               same_addr addr data ctrl fence hart E0 rf po.
  Let fpw := Frozen_mainmodel.frozen_ppo_wit Event Byte is_write is_read is_load is_store touches
               same_addr addr data ctrl fence E0 rf po d k.
  Let Rn := Rlift_mainmodel.Rn Event Byte Hart gmo is_write is_read touches hart E0 rf fpw d k.

  Theorem frozen_witness_passes_both_checks :
    (forall x, ~ clos_trans Event Cf x x) ->        (* fault per-location acyclic *)
    (forall x, ~ clos_trans Event FRf x x) ->       (* fault main-model acyclic (ppo discharged) *)
    (forall x, ~ clos_trans Event Cn x x) /\        (* witness per-location acyclic *)
    (forall x, ~ clos_trans Event Rn x x).          (* witness main-model acyclic *)
  Proof.
    intros Hcf Hfrf. split.
    - exact (Clift_coherence.witness_perloc_acyclic Event Byte gmo is_write is_read touches E0 rf
               poloc d k d_in d_w k_in k_w rf_touches keeper_before
               (Clift_coherence.Build_gmo_wf Event gmo E0 Htot) Hadj Hcf).
    - exact (Frozen_mainmodel.frozen_witness_mainmodel_acyclic Event eq_ev_dec Byte Hart gmo
               is_write is_read is_load is_store touches same_addr addr data ctrl fence hart E0 rf po
               d k d_in d_w k_in k_w kd_ne rf_touches keeper_before hart_dk Htot Hadj
               foot_dk po_twin rf_functional dup_r12 Hfrf).
  Qed.

End T1Frozen.
