(* Stage2_obligations.v — RESTART-V Stage-2: CLOSING the named semantic obligations O2 and O3, and
   DOCUMENTING O1 as the irreducible interface boundary.

   ===================================================================================================
   WHAT THIS FILE DOES — READ THIS BEFORE QUOTING ANYTHING BELOW
   ===================================================================================================
   `Stage2_state_chain.v` reduced Stage-2 `StateWF` to the STRUCTURAL half (discharged there,
   unconditionally) plus THREE NAMED SEMANTIC OBLIGATIONS O1 / O2 / O3, stated there as `Definition`s
   of `Prop` (so nothing assumes them anywhere).  This file turns "three named obligations" into
   "ONE irreducible interface fact":

     * O2  -- **CLOSED** (§1).
     * O3  -- **CLOSED / DISCHARGED** by genuine instantiation (§2).
     * O1  -- **NOT closed, and NOT closable here** (§3).  Documented, not proved.  No theorem in this
              file asserts O1 or anything that pretends to be O1.

   ---------------------------------------------------------------------------------------------------
   §1.  O2 IS CLOSED.
   ---------------------------------------------------------------------------------------------------
   O2 is the obligation Stage-2 Layer 3 (`Stage2_normal_candidate.v`, header item 3) **PAINTED ON** as
   `chk_ok_N (NChk _) := True`: that each GENERATED per-lane PMP check actually SUCCEEDS against the
   REPAIRED PMP state.

   `O2_closed` DERIVES it from `L3_handler`'s ALREADY-PROVED PMP algebra: the repaired table is
   literally `L3_handler.pupd Idx eq_idx Entry t dsg pmp_ok`, and the fact that the designated entry
   then holds `pmp_ok` is `L3_handler.pmp_update_designated` — REUSED, not restated and not reproved.
   `repair_is_local` is `L3_handler.pmp_update_local` applied, verbatim.

   THE RESIDUAL CONCRETE FACT is a SINGLE hypothesis:

       pmp_ok_grants : forall l, grants pmp_ok l

   i.e. "the repair VALUE written into the designated entry grants access to every lane's bytes".
   Concretely `pmp_ok = 0x1B = NAPOT|R|W` over the lane region, and this is EXACTLY what the handler
   binary certificate validates concretely — it is a primitive, certificate-validated property of ONE
   entry value, checked by inspecting one 8-bit configuration byte against one address range.

   THE REDUCTION THIS BUYS.  "Every lane check succeeds" is no longer a blanket operational
   assumption over an unbounded set of checks and states; it is now a THEOREM about every table `t`
   and every lane `l`, resting on one primitive property of one constant.  `O2_closes_state_chain_O2`
   then discharges `Stage2_state_chain.O2_normal_checks_succeed` itself, at this instantiation — so the
   obligation as NAMED THERE is inhabited here, not merely paralleled.

   ---------------------------------------------------------------------------------------------------
   §2.  O3 IS CLOSED — BY GENUINE INSTANTIATION, NOT BY A COMPOSITION-WITH-PREMISES.
   ---------------------------------------------------------------------------------------------------
   STATUS, PLAINLY:  O3 is **DISCHARGED**.  This is NOT the "state the composition theorem whose
   premises are the two proved statements" fallback.  `O3_reads_keep_values` APPLIES the proved
   Stage-1 theorem

       L1_abstract_erasure.L1_erasure_preserves_read_values

   to this file's variables and then pushes its conclusion through the proved Layer-3 transport

       Stage2_normal_candidate.transport_rf

   Neither proved statement appears as a premise of `O3_reads_keep_values`; both are CONSUMED by its
   proof term.  Its antecedents are only:
     (a) the interface hypotheses that `L1_erasure_preserves_read_values` ITSELF carries in its printed
         type — `rf_is_C4` (the C4 load-value rule realizes `rf`), `rf_touches`, `gmo_wf`; and
     (b) the duplicate-erasure setup — `DupPair p q`, `RO_K p q k`, `d = p \/ d = q`, `k <> d`.
   NONE of (a)/(b) is a restatement of the conclusion, and NONE was invented here: (a) is verbatim
   L1's section interface and (b) is verbatim L1's premise list.

   THE ONE MODELLING IDENTIFICATION, STATED OPENLY.  Layer 3's reads-from is a PARAMETER (`rf` of
   `Stage2_normal_candidate`'s section).  We instantiate that parameter at Stage-1's RETARGETED
   reads-from `L1_abstract_erasure.rf_retarget Event Byte d k rf` — which is precisely the reads-from
   that Stage 1 / `Ctx_erasure` hands over on the contracted carrier.  So `rf_N_ret` is not a new
   relation: it is Layer 3's own `rf_N` at the argument Layer 3 is meant to receive.

   WHAT O3 STILL DOES NOT SAY.  It does not say that the fault run's `rf` is the OPERATIONAL load
   value of the real machine; that is the model-interface commitment "the C4 rule is RVWMO's
   load-value rule", already named in the development and appearing here as `rf_is_C4`.  O3 closes the
   Stage-2 obligation ("normal-run reads return the fault run's values"), not that commitment.

   ---------------------------------------------------------------------------------------------------
   §3.  O1 IS **NOT** CLOSED AND IS **NOT CLOSABLE HERE**.  (Documentation only — NO theorem.)
   ---------------------------------------------------------------------------------------------------
   O1 says: the transition function used to GENERATE the normal state chain is the instruction model's
   REAL one (`Stage2_state_chain.O1_step_is_real`: `forall s e, step s e = real_transition s e`).

   It cannot be discharged inside this development.  Discharging it requires a bridge from our abstract
   `step` to the RATIFIED Sail operational model of RISC-V — and that bridge is exactly what the
   PARTIAL-VECTOR-EXECUTION barrier blocks: the ratified model does not expose the partial-execution
   states that a mid-vector trap and restart traverse, so there is nothing to equate our `step`
   against at the point where the argument needs it.

   O1 therefore has the SAME EPISTEMIC STATUS as the other model-interface facts this development
   already names — e.g. "the C4 rule is RVWMO's load-value rule" (`rf_is_C4` above), or "the frozen
   token grammar is the architectural one".  It is an INTERFACE COMMITMENT, not a theorem.

   CRUCIALLY: mechanizing OUR OWN operational semantics would **NOT** close O1.  It would only
   RELOCATE it.  The obligation is agreement with the RATIFIED model; a semantics we wrote ourselves
   would merely move the unproved equation from "our `step` = the ratified model" to "our mechanized
   semantics = the ratified model", with the same partial-vector-execution gap at the same place, and
   with a larger unaudited surface.  Writing more Coq cannot convert an interface commitment into a
   theorem.

   Accordingly §3 below contains ONLY a `Definition ... : Prop` restating O1 for citation.  There is
   no `Theorem`, no `Hypothesis`, no `Axiom`, and no `Admitted` about O1 anywhere in this file.

   ===================================================================================================
   STILL NOT PROVED ANYWHERE IN THE DEVELOPMENT
   ===================================================================================================
     * DECODING — that the frozen 71-instruction image decodes to the events used;
     * TOKEN CONFORMANCE;
     * the PRECISE-STATE condition;
     * the FULL FINAL-STATE CONSTRUCTION of the operational model / D-a `StateWF`.
   None of these is touched here.

   ===================================================================================================
   THE UPDATED LEDGER LINE, STATED PLAINLY
   ===================================================================================================
       Stage-2 state well-formedness
         = structural continuity                                        [ DISCHARGED ]
         + O2  "every generated lane check succeeds"                     [ CLOSED — this file §1,
                 modulo the certificate-validated constant `pmp_ok = 0x1B` ]
         + O3  "retained reads keep their fault-run values"              [ CLOSED / DISCHARGED —
                 this file §2 ]
         + O1  "`step` is the ratified model's transition function"      [ IRREDUCIBLE INTERFACE
                 BOUNDARY — not closed, not closable here ]
         + decoding / token conformance / precise-state / final-state    [ NAMED, OPEN ].

   AND, EMPHATICALLY: this still does **NOT** establish "there exists a no-fault EXECUTION".  Closing
   O2 and O3 removes two semantic residues from the state-well-formedness reduction; it does not build
   an execution of the ratified model, which remains blocked by O1 and by the four open items above.

   0 Admitted / 0 axioms (`Print Assumptions O2_closed`, `Print Assumptions O3_reads_keep_values`).
   No existing `.v` file is modified.  Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import RestartV.L3_handler.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Stage2_normal_candidate.
Require Import RestartV.Stage2_state_chain.
Import ListNotations.

(* =================================================================================================
   1.  O2 — CLOSED.  Derived from L3_handler's proved PMP algebra + ONE concrete fact.
   ================================================================================================= *)

Section O2Closure.

  Variable Idx Entry Lane : Type.
  Variable eq_idx : forall x y : Idx, {x = y} + {x <> y}.
  Variable dsg : Idx.                        (* THE designated repair entry (the frozen scope has one) *)
  Variable pmp_ok : Entry.                   (* the repair VALUE; concretely 0x1B = NAPOT|R|W *)
  Variable grants : Entry -> Lane -> Prop.   (* does this entry grant access to the lane's bytes? *)

  (* THE SINGLE RESIDUAL CONCRETE FACT.  It is exactly what the handler binary certificate validates:
     the designated entry receives `pmp_ok` = 0x1B = NAPOT|R|W over the lane region.  This is a
     primitive property of ONE entry value — one configuration byte against one address range — NOT a
     blanket assumption about checks, states or executions. *)
  Hypothesis pmp_ok_grants : forall l, grants pmp_ok l.

  Definition check_succeeds (t : Idx -> Entry) (l : Lane) : Prop := grants (t dsg) l.

  (* The repaired PMP table.  This is `L3_handler.pupd` itself — NOT a re-definition of it. *)
  Definition pmp_repaired (t : Idx -> Entry) : Idx -> Entry :=
    L3_handler.pupd Idx eq_idx Entry t dsg pmp_ok.

  (* ================================ HEADLINE (O2) ================================
     Every lane check succeeds against the repaired PMP state, for EVERY prior table `t` and EVERY
     lane `l`.  This is the fact Layer 3 painted on as `chk_ok_N`; here it is DERIVED. *)
  Theorem O2_closed : forall t l, check_succeeds (pmp_repaired t) l.
  Proof.
    intros t l. unfold check_succeeds, pmp_repaired.
    rewrite (L3_handler.pmp_update_designated Idx eq_idx Entry t dsg pmp_ok).
    apply pmp_ok_grants.
  Qed.

  (* The SAME fact with every local abbreviation unfolded, so that an auditor reading only the printed
     type sees the whole content: the entry that L3's PROVED update wrote at `dsg` grants every lane.
     Nothing is hidden inside `check_succeeds` / `pmp_repaired`. *)
  Theorem O2_closed_unfolded : forall (t : Idx -> Entry) (l : Lane),
    grants (L3_handler.pupd Idx eq_idx Entry t dsg pmp_ok dsg) l.
  Proof. intros t l. exact (O2_closed t l). Qed.

  (* Locality of the repair: nothing but the designated entry moves.  REUSED from L3, not reproved. *)
  Theorem repair_is_local : forall t q, q <> dsg -> pmp_repaired t q = t q.
  Proof.
    intros t q Hq.
    exact (L3_handler.pmp_update_local Idx eq_idx Entry t dsg pmp_ok q Hq).
  Qed.

  (* And the obligation AS NAMED IN `Stage2_state_chain` is inhabited at this instantiation:
     normal event universe := the lanes, machine state := the PMP table, repaired initial state :=
     `pmp_repaired t`, "is a check" := every lane, "the check succeeds in this state" :=
     `check_succeeds`.  So O2 is not merely paralleled here — the very `Prop` named there is proved. *)
  Theorem O2_closes_state_chain_O2 : forall t,
    Stage2_state_chain.O2_normal_checks_succeed
      Lane (Idx -> Entry) (pmp_repaired t)
      (fun _ : Lane => True)
      (fun (l : Lane) (tbl : Idx -> Entry) => check_succeeds tbl l).
  Proof.
    intros t l _. exact (O2_closed t l).
  Qed.

End O2Closure.

(* =================================================================================================
   2.  O3 — CLOSED.  Genuine instantiation of the proved Stage-1 theorem, pushed through the proved
       Layer-3 transport.  See header §2: this is a DISCHARGE, not a composition-with-premises.
   ================================================================================================= *)

Section O3Closure.

  (* ---- Stage-1's interface, VERBATIM the Variables of `L1_abstract_erasure.AbstractModel` ---- *)
  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte Value : Type.
  Variable is_write is_read : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable wval : Event -> Byte -> Value.
  Variable E0 : list Event.
  Variable gmo : Event -> Event -> Prop.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable po : Event -> Event -> Prop.

  (* ---- Layer 3's lane type (the only Layer-3 parameter O3's statement needs) ---- *)
  Variable Lane : Type.

  (* ---- Stage-1's TWO interface hypotheses, verbatim.  These are NOT added by this file: they
          appear in the printed type of `L1_erasure_preserves_read_values` itself.  `rf_is_C4` IS the
          model-interface commitment "the C4 rule is RVWMO's load-value rule". ---- *)
  Hypothesis rf_is_C4 :
    forall b r w, is_read r -> In r E0 -> rf w b r ->
      L1_abstract_erasure.C4_source Event Byte is_write touches gmo po E0 b r w.
  Hypothesis rf_touches : forall w b r, rf w b r -> touches w b.

  (* ---- The erased duplicate pair, its keeper `k` and the deleted copy `d` ---- *)
  Variable p q k d : Event.

  (* ================================ HEADLINE (O3) ================================
     Every retained read of the normal candidate has a normal-run reads-from source whose byte value
     equals the value its FAULT-run source supplied.  The witness `w'` and the value equation come
     from the proved Stage-1 theorem; the move into Layer 3's `rf_N` comes from the proved Layer-3
     transport.  Both are APPLIED here, not assumed.

     THE STATEMENT IS DELIBERATELY WRITTEN OUT IN FULL — no local abbreviations — so that its PRINTED
     TYPE exhibits, with nothing to unfold:
       * `L1_abstract_erasure.contract_carrier`      (Stage 1's surviving carrier),
       * `L1_abstract_erasure.rf_retarget`           (Stage 1's retargeted reads-from),
       * `Stage2_normal_candidate.rf_N` / `NKeep`    (Layer 3's OWN reads-from and injection).
     `rf_N` is a PARAMETERISED definition of `Stage2_normal_candidate`; supplying Stage 1's retargeted
     reads-from for its `rf` slot is exactly the intended composition, not a new construction. *)
  Theorem O3_reads_keep_values :
    L1_abstract_erasure.gmo_wf Event E0 gmo ->
    L1_abstract_erasure.DupPair Event Byte Value is_write touches wval p q ->
    L1_abstract_erasure.RO_K Event gmo po p q k ->
    (d = p \/ d = q) -> k <> d ->
    forall r b w,
      In r (L1_abstract_erasure.contract_carrier Event eq_ev_dec E0 d) ->
      is_read r -> rf w b r ->
      exists w' : Event,
        Stage2_normal_candidate.rf_N Event Byte Lane
          (L1_abstract_erasure.rf_retarget Event Byte d k rf)
          (Stage2_normal_candidate.NKeep Event Lane w') b
          (Stage2_normal_candidate.NKeep Event Lane r)
        /\ wval w' b = wval w b.
  Proof.
    intros Hwf Hdup Hrok Hdpq Hkd r b w Hr_in Hrd Hrf.
    (* Stage 1, PROVED: the retained read gets a retargeted source of equal byte value. *)
    destruct (L1_abstract_erasure.L1_erasure_preserves_read_values
                Event eq_ev_dec Byte Value is_write is_read touches wval E0 gmo rf po
                rf_is_C4 rf_touches Hwf
                p q k d r b w Hdup Hrok Hdpq Hkd Hr_in Hrd Hrf)
      as [w' [Hret Hval]].
    exists w'. split; [ | exact Hval ].
    (* Layer 3, PROVED: `rf_N` on the `NKeep` diagonal IS the underlying reads-from. *)
    apply (Stage2_normal_candidate.transport_rf Event Byte Lane
             (L1_abstract_erasure.rf_retarget Event Byte d k rf) w' b r).
    exact Hret.
  Qed.

  (* The obligation AS NAMED IN `Stage2_state_chain` is inhabited at this instantiation.  The
     per-event predicate is: "if this normal event is a retained read, then its fault-run source is
     matched by a normal-run source of equal value".  On a GENERATED check (`NChk _`) it is vacuous —
     correctly so: Layer 3's `chk_nonmem` says checks are non-memory, hence never loads. *)
  Definition load_agrees_N (n : Stage2_normal_candidate.NEv Event Lane) : Prop :=
    forall r b w, n = Stage2_normal_candidate.NKeep Event Lane r ->
      In r (L1_abstract_erasure.contract_carrier Event eq_ev_dec E0 d) ->
      is_read r -> rf w b r ->
      exists w' : Event,
        Stage2_normal_candidate.rf_N Event Byte Lane
          (L1_abstract_erasure.rf_retarget Event Byte d k rf)
          (Stage2_normal_candidate.NKeep Event Lane w') b
          (Stage2_normal_candidate.NKeep Event Lane r)
        /\ wval w' b = wval w b.

  Theorem O3_closes_state_chain_O3 :
    L1_abstract_erasure.gmo_wf Event E0 gmo ->
    L1_abstract_erasure.DupPair Event Byte Value is_write touches wval p q ->
    L1_abstract_erasure.RO_K Event gmo po p q k ->
    (d = p \/ d = q) -> k <> d ->
    Stage2_state_chain.O3_loads_agree
      (Stage2_normal_candidate.NEv Event Lane) load_agrees_N.
  Proof.
    intros Hwf Hdup Hrok Hdpq Hkd n.
    unfold load_agrees_N. intros r b w _ Hr_in Hrd Hrf.
    exact (O3_reads_keep_values Hwf Hdup Hrok Hdpq Hkd r b w Hr_in Hrd Hrf).
  Qed.

End O3Closure.

(* =================================================================================================
   3.  O1 — THE IRREDUCIBLE INTERFACE BOUNDARY.  DOCUMENTATION ONLY.
   -------------------------------------------------------------------------------------------------
   NOTHING BELOW IS A THEOREM, A HYPOTHESIS OR AN AXIOM.  §3 contains a single `Definition` of a
   `Prop`, provided so that other files and prose can CITE O1 by name.  Defining a `Prop` asserts
   nothing whatsoever.

   O1 is NOT proved here, and it is NOT provable here.  See header §3 for the full reasoning; in one
   sentence: the obligation is AGREEMENT WITH THE RATIFIED Sail model, the bridge to which is blocked
   by the partial-vector-execution barrier, so mechanizing our own operational semantics would
   RELOCATE O1 (from "our `step` = ratified model" to "our semantics = ratified model") rather than
   close it.  O1's epistemic status is that of the development's other model-interface commitments
   (e.g. `rf_is_C4` in §2 — "the C4 rule is RVWMO's load-value rule"), not that of a theorem.
   ================================================================================================= *)

Section O1InterfaceBoundary.

  Variable NEvT St : Type.
  Variable step : St -> NEvT -> St.               (* the transition function we FOLD to build the chain *)
  Variable ratified_transition : St -> NEvT -> St. (* the RATIFIED model's transition — abstract HERE, and
                                                      that is the whole point: we cannot reach it *)

  (* For citation only.  Identical in content to `Stage2_state_chain.O1_step_is_real`.  UNPROVED, and
     deliberately so: no `Theorem` in this development discharges it. *)
  Definition O1_is_an_interface_boundary : Prop :=
    forall s e, step s e = ratified_transition s e.

End O1InterfaceBoundary.

(* =================================================================================================
   END.  O2 closed (§1), O3 closed/discharged (§2), O1 documented as the irreducible interface
   boundary (§3, no theorem).  Decoding / token conformance / precise-state / final-state remain
   NAMED and OPEN, and "there exists a no-fault EXECUTION" remains UNPROVED.
   0 Admitted / 0 axioms.
   ================================================================================================= *)
