(* Stage2_state_chain.v — RESTART-V Stage-2 **LAYER 4**: the `StateWF` REDUCTION.

   ===================================================================================================
   WHAT THIS FILE IS — AND WHAT IT IS NOT.  READ THIS BEFORE QUOTING ANYTHING BELOW.
   ===================================================================================================
   This file **REDUCES** `StateWF`.  It does **NOT** prove `StateWF`.

   It discharges, unconditionally and for EVERY normal event list, the *STRUCTURAL* half of `StateWF`:
     * chain EXISTENCE — every list of normal events has a state chain, i.e. there are NO HOLES
       (`chain_total`);
     * ADJACENT-STATE CONTINUITY — the tail chain of `e :: l` starts at exactly `step s e`
       (`chain_adjacent`, and `chain_step_eq` which pins the head transition);
     * DETERMINISM — the chain from a given state over a given list has a unique end state
       (`chain_deterministic`);
     * COMPOSABILITY — chains concatenate, which is what Layer 3's carrier shape
       (`map NKeep mem_kernel ++ map NChk lanes`) needs (`chain_append`).

   The reason this is genuine content and not circular bookkeeping is one asymmetry:

     > The no-fault state chain is **GENERATED** by folding the transition function `step` from the
     > REPAIRED normal initial state `init_N`.  Adjacency therefore holds **BY CONSTRUCTION**: the
     > `ChainStep` constructor can only be applied at `step s e`, so no proof obligation about
     > "do these two states line up?" ever arises.
     >
     > This is EXACTLY what copying the fault run's states cannot deliver.  The no-fault initial PMP
     > state is ALREADY REPAIRED, so the fault run's pre/post states are not the states of any normal
     > chain, and deleting the trap/handler events from the fault run leaves the copied states
     > NON-ADJACENT (GPT Pro's observation).  Generation, not copying, is what buys the structural half.

   `chain_total` is proved by induction on the list; `chain_deterministic` and `chain_append` by
   induction on the `Chain` derivation.  Nothing structural is assumed: see the printed type of the
   headline — it is universally quantified over `NEvT`, `St`, `step`, `init_N` and mentions NO
   hypothesis whatsoever.

   ---------------------------------------------------------------------------------------------------
   ANTI-VACUITY.  The headline's antecedent list is EMPTY.  `StateWF_struct` is not assumed anywhere,
   under any name, in any form; it is derived from `chain_total` and `chain_deterministic`, which are
   derived from the inductive definition of `Chain`.  No hypothesis in this file re-asserts a conjunct
   of any conclusion of this file.
   ---------------------------------------------------------------------------------------------------

   ===================================================================================================
   WHAT IS **NOT** PROVED HERE
   ===================================================================================================
   (O1) That `step` is the instruction model's REAL transition function.  `step` is an abstract
        *parameter* of this file, so NOTHING about RISC-V semantics is asserted, computed or checked.
        Every theorem below is a statement about folding an arbitrary function; the claim "this fold is
        the RISC-V normal execution" is precisely the open obligation.
   (O2) That each GENERATED per-lane check actually SUCCEEDS against the repaired PMP state.  This is
        exactly the operational fact that Stage-2 Layer 3 (`Stage2_normal_candidate.v`, header item 3)
        **painted on** as `chk_ok_N (NChk _) := True`.  NAMING it here is the point; it is NOT proved
        here and it is NOT assumed here either (it is a `Definition` of a Prop, see §4).
   (O3) That normal-run load values agree with the fault run's.  (Layer 3's `rf` transport is what
        would supply this; it is named, not established.)

   ALSO NOT PROVED, and outside the scope of this file entirely:
     * DECODING (that the frozen 71-instruction image decodes to the events used),
     * TOKEN CONFORMANCE,
     * the PRECISE-STATE condition,
     * the FULL FINAL-STATE CONSTRUCTION of the D-a `StateWF`.

   ===================================================================================================
   NET EFFECT ON THE PROJECT'S HONESTY LEDGER
   ===================================================================================================
   The ledger entry

       "general Stage-2 `StateWF`: not done"

   becomes

       "`StateWF` = structural continuity (**DISCHARGED**) + O1/O2/O3 + decoding / token conformance /
        precise-state (**NAMED, OPEN**)".

   The remaining surface is now PRECISE and SMALL.  It is **NOT CLOSED**.

   ===================================================================================================
   REUSE OF THE PROVED L3 HANDLER RESULT (not an assumption)
   ===================================================================================================
   The replay-boundary U-view fact is obtained FROM `RestartV.L3_handler.handler_preserves_U`, a
   THEOREM proved there (0 axioms), instantiated at this file's register/value types — it is NOT
   restated as a hypothesis.  `handler_restores_xT` is likewise cited (it is the `r = xT` case that
   `handler_preserves_U` internally consumes, and it is re-exposed here as
   `replay_boundary_xT_restored`).

   FLAGGED — the ONE type-bridging device: `Variable regs : St -> (Reg -> Value)`.  This file's machine
   state `St` is abstract, while `L3_handler`'s state is literally `Reg -> Value`.  `regs` is a
   PROJECTION (a view of the abstract state as a register file), NOT a smuggled assumption: it asserts
   no property of anything, it only says "an abstract state has a register-file view".  Saying so is
   required by the reporting discipline.  The equation that a particular step IS the handler
   (`regs (step s e) = uview_after_handler s`) is likewise NOT assumed globally: it appears as an
   explicit ANTECEDENT of `handler_step_preserves_uview`, i.e. a modelling equation the caller must
   supply, and it is part of O1.

   ===================================================================================================
   THE HONEST BOTTOM LINE
   ===================================================================================================
   Composed with `Ctx_erasure.general_ctx_erasure` and `Stage2_normal_candidate.stage2_normal_candidate`,
   the development still does **NOT** establish "there exists a no-fault EXECUTION".  What it
   establishes is: a trap-free, structurally-normal, RVWMO-consistent MEMORY KERNEL whose state chain is
   STRUCTURALLY WELL-FORMED (generated, hole-free, continuous, deterministic, composable), with the
   residual SEMANTIC obligations O1/O2/O3 and the decoding / token / precise-state obligations NAMED and
   OPEN.  "There exists a no-fault EXECUTION" remains unproved.

   0 Admitted / 0 axioms (`Print Assumptions stage2_statewf_reduction`).  Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import RestartV.L3_handler.
Import ListNotations.

(* =================================================================================================
   1.  THE GENERATED STATE CHAIN — the structural half, discharged.
   ================================================================================================= *)

Section Stage2StateChain.

  Variable NEvT : Type.              (* the normal event universe (Layer 3's `NEv`, kept abstract) *)
  Variable St   : Type.              (* machine state *)
  Variable step : St -> NEvT -> St.  (* the normal transition function — a PARAMETER: see (O1) *)
  Variable init_N : St.              (* Sigma_N^0, the REPAIRED normal initial state *)

  (* The state chain.  Note the shape of `ChainStep`: its premise is a chain starting at `step s e`,
     NOT at some arbitrary "next state" that would then have to be RELATED to `s`.  Adjacency is thus
     not a side condition to be proved — it is the only way to build the constructor. *)
  Inductive Chain : St -> list NEvT -> St -> Prop :=
  | ChainNil  : forall s, Chain s [] s
  | ChainStep : forall s e l s', Chain (step s e) l s' -> Chain s (e :: l) s'.

  (* ---- 1.1  TOTALITY: no holes.  Every normal event list has a chain. ---- *)
  Theorem chain_total : forall l s, exists s', Chain s l s'.
  Proof.
    induction l as [| e l IH]; intro s.
    - exists s. apply ChainNil.
    - destruct (IH (step s e)) as [s' H]. exists s'. apply ChainStep. exact H.
  Qed.

  (* ---- 1.2  DETERMINISM. ---- *)
  Theorem chain_deterministic : forall l s s1 s2, Chain s l s1 -> Chain s l s2 -> s1 = s2.
  Proof.
    induction l as [| e l IH]; intros s s1 s2 H1 H2.
    - inversion H1; subst; inversion H2; subst; reflexivity.
    - inversion H1 as [| s0 e0 l0 sa Ha]; subst.
      inversion H2 as [| s1' e1 l1 sb Hb]; subst.
      exact (IH (step s e) s1 s2 Ha Hb).
  Qed.

  (* ---- 1.3  ADJACENT-STATE CONTINUITY: the tail chain starts EXACTLY at `step s e`. ---- *)
  Theorem chain_adjacent : forall s e l s', Chain s (e :: l) s' -> Chain (step s e) l s'.
  Proof.
    intros s e l s' H. inversion H as [| s0 e0 l0 sa Ha]; subst. exact Ha.
  Qed.

  (* The continuity witness in "there is an intermediate state and it is the step-image" form: the
     head state of the tail is not merely SOME state, it is provably `step s e`. *)
  Theorem chain_step_eq :
    forall s e l s', Chain s (e :: l) s' ->
      exists sm, sm = step s e /\ Chain sm l s'.
  Proof.
    intros s e l s' H. exists (step s e). split; [reflexivity | apply chain_adjacent; exact H].
  Qed.

  (* ---- 1.4  COMPOSABILITY: needed because Layer 3's carrier is `map NKeep .. ++ map NChk ..`. ---- *)
  Theorem chain_append :
    forall l1 l2 s sm s', Chain s l1 sm -> Chain sm l2 s' -> Chain s (l1 ++ l2) s'.
  Proof.
    intros l1 l2 s sm s' H1. revert l2 s'.
    induction H1 as [ s0 | s0 e l sa H IH ]; intros l2 s' H2.
    - simpl. exact H2.
    - simpl. apply ChainStep. apply IH. exact H2.
  Qed.

  (* Corollary in the exact shape a two-block carrier needs: the concatenation is total and its end
     state is the fold through the intermediate state. *)
  Theorem chain_append_total :
    forall l1 l2 s, exists sm s', Chain s l1 sm /\ Chain sm l2 s' /\ Chain s (l1 ++ l2) s'.
  Proof.
    intros l1 l2 s.
    destruct (chain_total l1 s) as [sm H1].
    destruct (chain_total l2 sm) as [s' H2].
    exists sm, s'. split; [exact H1|]. split; [exact H2|].
    exact (chain_append l1 l2 s sm s' H1 H2).
  Qed.

  (* ---- 1.5  The STRUCTURAL half of `StateWF`. ---- *)
  Definition StateWF_struct (l : list NEvT) : Prop :=
    (exists s', Chain init_N l s')
    /\ (forall s1 s2, Chain init_N l s1 -> Chain init_N l s2 -> s1 = s2).

  Theorem statewf_struct_holds : forall l, StateWF_struct l.
  Proof.
    intro l. unfold StateWF_struct. split.
    - apply chain_total.
    - intros s1 s2 H1 H2. exact (chain_deterministic l init_N s1 s2 H1 H2).
  Qed.

  (* =============================== HEADLINE =============================== *)
  (* The structural half of `StateWF` is discharged UNCONDITIONALLY for EVERY normal event list,
     together with the append lemma the Layer-3 carrier shape needs, and the adjacency witness.
     O1/O2/O3 are deliberately NOT bundled in: the whole point of the reduction is that the
     structural half needs NONE of them. *)
  Theorem stage2_statewf_reduction : forall l,
    StateWF_struct l
    /\ (forall l1 l2 s sm s', Chain s l1 sm -> Chain sm l2 s' -> Chain s (l1 ++ l2) s')
    /\ (forall s e l' s', Chain s (e :: l') s' -> Chain (step s e) l' s').
  Proof.
    intro l. split; [ apply statewf_struct_holds | ].
    split; [ exact chain_append | exact chain_adjacent ].
  Qed.

End Stage2StateChain.

(* =================================================================================================
   2.  THE REPLAY-BOUNDARY U-VIEW FACT — REUSED from `L3_handler`, not assumed.
   ================================================================================================= *)

Section Stage2ReplayBoundary.

  Variable St : Type.
  Variable Reg Value : Type.
  Variable eq_reg : forall x y : Reg, {x = y} + {x <> y}.

  (* FLAGGED PROJECTION (see header): the register-file view of the abstract machine state.  This
     asserts no property of anything; it only bridges `St` to `L3_handler`'s `State = Reg -> Value`. *)
  Variable regs : St -> L3_handler.State Reg Value.

  Definition uview (s : St) : Reg -> Value := regs s.

  (* L3's handler interface, instantiated verbatim (same names, same shape as `L3_handler.Handler`). *)
  Variables xT mscratch : Reg.
  Hypothesis xT_ms_distinct : xT <> mscratch.
  Variable body : L3_handler.State Reg Value -> L3_handler.State Reg Value.
  Hypothesis body_only_xT : forall s r, r <> xT -> body s r = s r.

  (* the U view AFTER the handler has run, expressed with L3's OWN `handler` definition *)
  Definition uview_after_handler (s : St) : Reg -> Value :=
    L3_handler.handler Reg eq_reg Value xT mscratch body (regs s).

  (* ---- (5) The replay-boundary fact, obtained FROM the proved L3 theorem
              `L3_handler.handler_preserves_U`. ---- *)
  Theorem replay_boundary_uview_preserved :
    forall (s : St) (r : Reg), r <> mscratch -> uview_after_handler s r = uview s r.
  Proof.
    intros s r Hr. unfold uview_after_handler, uview.
    exact (L3_handler.handler_preserves_U
             Reg eq_reg Value xT mscratch xT_ms_distinct body body_only_xT (regs s) r Hr).
  Qed.

  (* the xT half, from `L3_handler.handler_restores_xT` *)
  Theorem replay_boundary_xT_restored :
    forall s : St, uview_after_handler s xT = uview s xT.
  Proof.
    intro s. unfold uview_after_handler, uview.
    exact (L3_handler.handler_restores_xT
             Reg eq_reg Value xT mscratch xT_ms_distinct body body_only_xT (regs s)).
  Qed.

  (* ---- The bridge from the L3 fact to the GENERATED chain of §1. ----
     `chain_preserves_uview` is genuine induction: its antecedent is about ONE step, its conclusion
     about an ARBITRARY chain, so it is not a restatement.  It is the reason the structural chain and
     the L3 handler result compose. *)
  Variable NEvT : Type.
  Variable step : St -> NEvT -> St.

  Theorem chain_preserves_uview :
    (forall s e r, r <> mscratch -> regs (step s e) r = regs s r) ->
    forall l s s', Chain NEvT St step s l s' ->
      forall r, r <> mscratch -> regs s' r = regs s r.
  Proof.
    intros Hstep l s s' H.
    induction H as [ s0 | s0 e l0 sa H IH ]; intros r Hr.
    - reflexivity.
    - rewrite (IH r Hr). exact (Hstep s0 e r Hr).
  Qed.

  (* And the per-step premise IS supplied by L3 at any event whose transition is the handler.  The
     modelling equation `regs (step s e) = uview_after_handler s` is an explicit ANTECEDENT here (part
     of O1), NOT a global hypothesis. *)
  Theorem handler_step_preserves_uview :
    forall s e, regs (step s e) = uview_after_handler s ->
      forall r, r <> mscratch -> regs (step s e) r = regs s r.
  Proof.
    intros s e Heq r Hr. rewrite Heq.
    exact (replay_boundary_uview_preserved s r Hr).
  Qed.

End Stage2ReplayBoundary.

(* =================================================================================================
   3.  THE NAMED SEMANTIC RESIDUE — O1/O2/O3.
   -------------------------------------------------------------------------------------------------
   These are stated as `Definition`s of `Prop`, NOT as `Hypothesis`es.  That is deliberate and is
   STRICTLY MORE HONEST than assuming them: nothing in this file assumes them, so no theorem here is
   contaminated, and the reduction theorem below takes them as EXPLICIT arrows so that anyone reading
   the printed type sees exactly what is owed.  NONE of O1/O2/O3 is proved anywhere in this
   development.
   ================================================================================================= *)

Section Stage2NamedResidue.

  Variable NEvT : Type.
  Variable St : Type.
  Variable step : St -> NEvT -> St.
  Variable init_N : St.

  (* (O1) `step` is the instruction model's real transition function for normal events.
          Modelled by comparing the abstract parameter `step` against the (equally abstract here)
          real transition relation of the instruction model.  NOT proved: this file makes no claim
          about RISC-V semantics; `step` is a parameter. *)
  Variable real_transition : St -> NEvT -> St.
  Definition O1_step_is_real : Prop := forall s e, step s e = real_transition s e.

  (* (O2) every GENERATED per-lane check succeeds against `init_N`'s REPAIRED PMP state.
          This is exactly the operational fact Layer 3 painted on as `chk_ok_N`
          (`Stage2_normal_candidate.v`, header item 3).  Supplied by: nothing yet.  OPEN. *)
  Variable is_chk_like : NEvT -> Prop.          (* abstract, per the design *)
  Variable chk_succeeds_in : NEvT -> St -> Prop.
  Definition O2_normal_checks_succeed : Prop :=
    forall c, is_chk_like c -> chk_succeeds_in c init_N.

  (* (O3) load values in the normal run agree with the fault run's.
          Would be supplied by Layer 3's `rf` transport (`Stage2_normal_candidate.transport_rf`)
          together with an operational read-value lemma.  OPEN. *)
  Variable load_agrees : NEvT -> Prop.
  Definition O3_loads_agree : Prop := forall e, load_agrees e.

  (* The reduction TARGET: the structural half PLUS the three named semantic obligations. *)
  Definition StateWF_target (l : list NEvT) : Prop :=
    StateWF_struct NEvT St step init_N l
    /\ O1_step_is_real /\ O2_normal_checks_succeed /\ O3_loads_agree.

  (* THE REDUCTION, spelled out: the target follows from O1/O2/O3 ALONE.  The structural conjunct is
     NOT among the antecedents — it is discharged by `statewf_struct_holds`.  That asymmetry is the
     entire content of this file. *)
  Theorem statewf_target_reduces_to_O123 :
    O1_step_is_real -> O2_normal_checks_succeed -> O3_loads_agree ->
    forall l, StateWF_target l.
  Proof.
    intros H1 H2 H3 l. unfold StateWF_target.
    split; [ apply statewf_struct_holds | ].
    split; [ exact H1 | ]. split; [ exact H2 | exact H3 ].
  Qed.

  (* Explicitly recorded NON-result: this file does NOT prove any of O1/O2/O3, and does not prove
     decoding, token conformance, the precise-state condition, or the full final-state construction.
     Consequently it does NOT establish "there exists a no-fault EXECUTION". *)

End Stage2NamedResidue.
