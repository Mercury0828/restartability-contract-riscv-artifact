(* Top_T1_skeleton.v — RESTART-V M4: the acyclicity-transfer step used by the T1 argument.

   HONESTY NOTE (revised after round-11 blind audit). This file does NOT compose the layer
   developments into a T1 theorem, and its main lemma is NOT T1. It isolates ONE order-theoretic
   step that the eventual T1 consistency-preservation argument needs, and states it over ARBITRARY
   relations so it can later be instantiated:

       if the fault-run relation is acyclic and every no-fault-witness edge lifts to a fault-run
       path, then the witness relation is acyclic.

   The two hypotheses `Rlift` / `Clift` (that each witness edge is supported by a fault-run path) are
   the T1-specific content. They are UNPROVEN in THIS file (it is `acyclic_via_simulation` applied
   twice over arbitrary relations). The two companion files each prove a matching lift for the
   concrete erasure relations —
     - Clift_coherence.`Cn_lifts` / `witness_perloc_acyclic` : every witness per-location edge
       (co ∪ rf ∪ fr ∪ po-loc) lifts to a clos_trans-Cf path (rf retarget via the two-edge path
       k ->co d ->rf r).
     - Rlift_mainmodel.`Rn_lifts` / `witness_mainmodel_acyclic` : every witness main-model edge
       (co ∪ rfe ∪ fr ∪ ppo) lifts likewise, MODULO the single explicit `ppo_lifts` obligation.
   The composition IS now a Coq term: `T1_consistency.witness_passes_both_checks` (a separate file)
   `Require`s both companions and applies `witness_perloc_acyclic` + `witness_mainmodel_acyclic`
   under shared parameters, proving "fault run consistent + ppo edges lift ⇒ the witness passes BOTH
   RVWMO acyclicity checks". So the abstract transfer here is genuinely composed downstream.

   HONESTY NOTE (round-13 audit). What the composition still does NOT do: nothing yet proves that the
   Cn/Cf/Rn/Rf fed to it are the relations of ONE concrete execution obtained from L1's
   `contract_carrier` / `rf_retarget` — they are supplied abstractly. And the fault run's two
   acyclicity checks are hypotheses (the fault run is ASSUMED consistent).

   What still remains for the whole T1: discharge `ppo_lifts` (concrete PPO r1-r13 under erasure);
   construct the concrete witness execution and prove its relations ARE L1's contracted relations;
   discharge L1-L4's interfaces from that model; and conclude the ∀fault∃no-fault OBSERVATIONAL-
   refinement statement (the observation projection O and R0 — the part beyond consistency-
   preservation). None of that is in this file. Coq 8.15. *)

Require Import Coq.Relations.Relations.
Require Import RestartV.L2_ppo.

Section AcyclicityTransfer.

  Variable Event : Type.

  (* Main-model union (co∪rfe∪fr∪ppo) and per-location coherence union (co∪rf∪fr∪po-loc),
     for the fault run (…f) and the intended no-fault witness (…n). These are placeholders: nothing
     here constrains them to be those unions or to come from any execution. *)
  Variables Rf Rn Cf Cn : Event -> Event -> Prop.

  (* Sufficient condition for witness consistency, ASSUMING the edge-lift facts. The name says what
     it is: acyclicity of the witness given the lift, not a T1 theorem. *)
  Theorem witness_acyclic_if_edges_lift :
    (* fault run acyclic: main-model and per-location relations *)
    (forall x, ~ clos_trans Event Rf x x) ->
    (forall x, ~ clos_trans Event Cf x x) ->
    (* UNPROVEN T1-specific obligation: every witness edge lifts to a fault-run path *)
    (forall x y, Rn x y -> clos_trans Event Rf x y) ->
    (forall x y, Cn x y -> clos_trans Event Cf x y) ->
    (* THEN the witness relations are acyclic *)
    (forall x, ~ clos_trans Event Rn x x) /\
    (forall x, ~ clos_trans Event Cn x x).
  Proof.
    intros HRf HCf HRlift HClift. split.
    - exact (acyclic_via_simulation Event Rf Rn HRlift HRf).
    - exact (acyclic_via_simulation Event Cf Cn HClift HCf).
  Qed.

End AcyclicityTransfer.

(* Inventory of the mechanized pieces (each 0 Admitted / 0 axioms), stated as CONDITIONAL kernels —
   they machine-check that certain premises SUFFICE, and leave the premises' discharge from the
   concrete D-a model as future work:
   - L1_abstract_erasure: given the section C4/gmo interface + gamma_adj + RO-K, contraction
     preserves the L1 consistency record and read values.
   - L2_gamma: gamma_D + (r1, po-comparability, po-envelope, gmo_wf) => gamma_adj  [sufficiency only;
     gamma_E undefined, strictness unproven].
   - L2_consistency: co/rfe/fr ⊆ gmo, "a carrier-relation ⊆ gmo is acyclic", AND the concrete
     main-model union co∪rfe∪fr∪ppo assembled + proven acyclic (`Main_model_acyclic`), reduced to
     the single obligation ppo⊆gmo [PPO r1-r13 remains].
   - L2_ppo: C3B acyclicity FROM a rank classification [H_co/H_rf/H_fr/H_poloc assumed], plus the
     acyclic_via_simulation transfer lemma used above.
   - L3_handler: state-update algebra for the save/body/restore shape [body_only_xT assumed; no
     instruction semantics], and functional PMP update locality [no pmp_ok encoding].
   - L4_restart: both restart-reading records feed L1's reduced RO interface; the Re-execution
     keeper is now DERIVED (gmo p q from CoWW + co⊆gmo, not assumed) [still no full execution
     semantics; Continuation's coherence direction is inherent].
   The boundary between "mechanized" and "assumed" is exactly the set of bracketed premises above. *)
