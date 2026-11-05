(* Adapter_L1_witness.v — RESTART-V M4: identify Clift's abstract witness relations with L1's
   concrete contracted execution. First step of the "connect abstract to concrete" work that the
   round-13/14 audits named as the main open gap in the composition.

   Clift_coherence states its witness relations over an abstract `survivor` predicate
   (In E0 ∧ ≠ d) and an abstract `rfw` retarget. L1 constructs the actual contracted execution with
   `contract_carrier d` (= filter d out of E0) and `rf_retarget d k rf`. This file proves they
   coincide pointwise:

     - `survivor_iff_contract`   : survivor x  ↔  In x (contract_carrier d)
     - `rfw_eq_retarget`         : Clift.rfw   ↔  L1.rf_retarget           (definitional)
     - `co_wit_iff_contract`     : Clift.co_wit ↔ coherence over the contracted carrier

   Consequence (stated, not re-proved here): Clift_coherence.`witness_perloc_acyclic` and hence
   T1_consistency.`witness_passes_both_checks` are, after this identification, statements about the
   ACTUAL carrier `contract_carrier d` with rf `rf_retarget d k rf` — no longer about arbitrary
   relations. What still remains to fully close the gap: the analogous identification for the
   main-model (Rlift) relations and for the fault-run co/fr/rf as L1's E0-relations, plus supplying
   the concrete witness PPO and its `ppo_lifts`. Self-contained modulo L1 + Clift; 0 Admitted /
   0 axioms (Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Clift_coherence.
Import ListNotations.

Section Adapter.

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte : Type.
  Variable gmo : Event -> Event -> Prop.
  Variable is_write : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable E0 : list Event.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variables d k : Event.

  Notation CC := (L1_abstract_erasure.contract_carrier Event eq_ev_dec E0 d).

  (* 1. The survivor predicate is exactly membership in L1's contracted carrier. *)
  Lemma survivor_iff_contract :
    forall x, Clift_coherence.survivor Event E0 d x <-> In x CC.
  Proof.
    intro x. unfold Clift_coherence.survivor. split.
    - intros [Hin Hne].
      apply (L1_abstract_erasure.In_contract Event eq_ev_dec E0 d x Hin Hne).
    - intro H. split.
      + apply (L1_abstract_erasure.contract_carrier_sub Event eq_ev_dec E0 d x H).
      + apply (L1_abstract_erasure.contract_carrier_not_d Event eq_ev_dec E0 d x H).
  Qed.

  (* 2. Clift's retargeted rf is definitionally L1's rf_retarget. *)
  Lemma rfw_eq_retarget :
    forall w b r,
      Clift_coherence.rfw Event Byte rf d k w b r <->
      L1_abstract_erasure.rf_retarget Event Byte d k rf w b r.
  Proof.
    intros w b r. split; intro H; exact H.
  Qed.

  (* 3. Clift's witness coherence is coherence over the contracted carrier. *)
  Lemma co_wit_iff_contract :
    forall b w1 w2,
      Clift_coherence.co_wit Event Byte gmo is_write touches E0 d b w1 w2 <->
      (In w1 CC /\ In w2 CC /\ is_write w1 /\ is_write w2 /\
       touches w1 b /\ touches w2 b /\ gmo w1 w2).
  Proof.
    intros b w1 w2. unfold Clift_coherence.co_wit, Clift_coherence.coOn. split.
    - intros [S1 [S2 [W1 [W2 [T1 [T2 G]]]]]].
      split; [apply (proj1 (survivor_iff_contract w1)); exact S1|].
      split; [apply (proj1 (survivor_iff_contract w2)); exact S2|].
      split; [exact W1|]. split; [exact W2|]. split; [exact T1|]. split; [exact T2|]. exact G.
    - intros [I1 [I2 [W1 [W2 [T1 [T2 G]]]]]].
      split; [apply (proj2 (survivor_iff_contract w1)); exact I1|].
      split; [apply (proj2 (survivor_iff_contract w2)); exact I2|].
      split; [exact W1|]. split; [exact W2|]. split; [exact T1|]. split; [exact T2|]. exact G.
  Qed.

  (* 4. Clift's witness fr edge is fr over the contracted execution (source via rf_retarget, the
     coherence-later write over the contracted carrier). Composes lemmas 2 and 3. *)
  Lemma fr_wit_iff_contract :
    forall b r w2,
      Clift_coherence.fr_wit Event Byte gmo is_write touches E0 rf d k b r w2 <->
      (exists w1, L1_abstract_erasure.rf_retarget Event Byte d k rf w1 b r /\
                  (In w1 CC /\ In w2 CC /\ is_write w1 /\ is_write w2 /\
                   touches w1 b /\ touches w2 b /\ gmo w1 w2)).
  Proof.
    intros b r w2. unfold Clift_coherence.fr_wit. split.
    - intros [w1 [Hrfw Hco]]. exists w1. split.
      + apply (proj1 (rfw_eq_retarget w1 b r)); exact Hrfw.
      + apply (proj1 (co_wit_iff_contract b w1 w2)); exact Hco.
    - intros [w1 [Hret Hco]]. exists w1. split.
      + apply (proj2 (rfw_eq_retarget w1 b r)); exact Hret.
      + apply (proj2 (co_wit_iff_contract b w1 w2)); exact Hco.
  Qed.

End Adapter.
