(* Stage2_endtoend_v2.v — RESTART-V: guarded-PPO Stage-2 capstone.
   SUPERSEDES `Stage2_endtoend.v`; that file remains unchanged.

   ===================================================================================================
   WHY THIS FILE EXISTS — THREE VERIFIED DEFECTS OF `Stage2_composed.v`
   ===================================================================================================
   A hostile review of `Stage2_composed.v` found three defects, all of which this file repairs.  None
   of them is a wording problem; each is a mechanized-content problem.

   D1.  `Stage2_composed` NEVER APPLIES `frozen_T1_refinement`.  Its proof term does not mention T1 at
        all, so the "composition" does not consume the T1 theorem it is advertised as composing with.

   D2.  `Stage2_composed` TRANSPORTS THE WRONG RELATION.  It transports `Clift_coherence.Cf`
        instantiated at a *witness* carrier.  But `Cf`'s `rf` and `po-loc` disjuncts carry **no**
        carrier membership at all (see `Clift_coherence.v` lines 69-73), whereas `Cn` adds `survivor`
        to **every** disjunct — that was the round-15 audit fix, recorded in the comment at
        `Clift_coherence.v:74`.  Therefore `Cf` instantiated at a carrier `E` is a strict
        SUPER-relation of `E`'s per-location relation, and T1's conclusion (`Cn` acyclic) does NOT
        imply the `Cf`-at-a-carrier acyclicity that `Stage2_composed` assumes.  There is no implication
        between the two, in either direction, and `Stage2_composed` supplies none.

   D3.  `Stage2_composed` CARRIES ONLY ONE OF THE TWO RVWMO CHECKS.  RVWMO consistency is
        acyclic(co u rf u fr u po-loc) AND acyclic(co u rfe u fr u ppo).  `Stage2_composed.v` and
        `Ctx_erasure.v` contain ZERO occurrences of `Rn` / `rfe` / `ppo` / `Rlift`.  The main-model
        check is simply absent from the chain.

   ===================================================================================================
   WHAT THIS FILE DOES INSTEAD  (the four requirements, all met — see the report at the foot)
   ===================================================================================================
   R1. IT APPLIES `T1_frozen_refinement.frozen_T1_refinement`.  `T1_OUT` below is a `Definition` whose
       body IS that theorem applied to this file's variables and hypotheses; every downstream
       acyclicity/observation fact is obtained by destructing `T1_OUT`.  T1 is CONSUMED by the proof
       term, exactly as `Stage2_obligations.O3_reads_keep_values` consumes
       `L1_erasure_preserves_read_values`.  (Repairs D1.)

   R2. IT TRANSPORTS T1's OWN OUTPUTS, `Cn` AND `Rn` — NEVER `Cf`.  `Cf` appears in this file in
       exactly one place: as the FAULT run's per-location relation at the FAULT carrier `E0`, which is
       literally T1's own antecedent `Hfault_perloc`.  It is never used as any target carrier's
       relation.  To move `Cn` / `Rn` along a carrier chain we need them as functions OF the carrier,
       which `Clift_coherence.Cn` / `Rlift_mainmodel.Rn` are not (their carrier is hard-wired to
       `survivor = In E0 /\ <> d`).  So §A defines the carrier-parameterised `CnC C` / `RnC C`.
       `RnC` guards PPO endpoints too.  Its identification with canonical `Rn` uses the proved
       `frozen_ppo_wit_endpoints` lemma, by destructing every frozen PPO constructor; it is not
       asserted by conversion.  (Repairs D2 and the round-4 PPO-carrier defect.)

   R3. IT CARRIES **BOTH** CHECKS ALONG `E_C -> E_K -> E_MK -> E_N`.  §B proves that `CnC` is
       unchanged by memory-silent erasure.  It deliberately proves only `Rn_target ⊆ Rn_source`:
       memory silence does not exclude fence/dependency PPO endpoints, so the reverse direction is
       unavailable without another premise.  This subrelation is exactly what transports
       acyclicity.  §C then reflects and injects the guarded relation across `NKeep`.

   R4. IT INSTANTIATES O2 AND O3 AT THE WIRED CHAIN.  `Stage2_obligations.O3_reads_keep_values` is
       applied at THIS file's `E0/rf/p/q/k/d`, so its conclusion is about `contract_carrier ... d`
       (= `E_C`) and `rf_retarget d k rf` (= `rf_C`) — the very objects the chain carries.
       O2 additionally requires a nonempty complete lane list, coverage of `0..VL-1`, injectivity and
       range of `lane_index`, and an exact byte-address footprint for each kernel lane-write.
       `Stage2_obligations.O2_closed` is then instantiated with a non-implicational concrete grant.

   ===================================================================================================
   WHAT IS **NOT** CARRIED — READ THIS BEFORE QUOTING ANYTHING BELOW
   ===================================================================================================
   * THE ANTECEDENTS ARE THE **FAULT** RUN's.  The headline's two consistency antecedents are
     `Hfault_perloc` (acyclicity of `Clift_coherence.Cf` at the FAULT carrier `E0`, with the FAULT
     `rf`/`po-loc`) and `Hfault_main` (acyclicity of `Frozen_mainmodel.FRf` at `E0`).  These are
     T1's own antecedents, verbatim.  The TARGET's acyclicity — of `Cn`/`Rn` at `E_C`, `E_K`, `E_MK`
     or `E_N` — is NOWHERE among the hypotheses; it is DERIVED.  That is the whole point, and it is
     checkable from the printed type of `stage2_endtoend_v2`.
   * `Cf` AT `E0` IS ITSELF A SUPER-RELATION of the fault run's per-location relation (its `rf` and
     `po-loc` disjuncts are carrier-free).  Assuming acyclicity of a super-relation is a STRONGER
     antecedent than assuming acyclicity of the real one, so this is conservative in the safe
     direction — but it IS a strengthening of the premise and is flagged here.  It is inherited from
     `Clift_coherence` / T1 and is not introduced by this file.
   * `E_N` IS A MEMBER OF `Cand_N_struct`, NOT OF THE OPERATIONAL `Cand_N`.  Layer 3's structural
     rendering is strictly weaker (see `Stage2_normal_candidate.v` header items 1-5).  Nothing here
     constructs an execution, a state chain over the real semantics, or a trap-free operational run.
   * `StateWF` IS NOT ESTABLISHED.  O1 (`step` is the ratified transition function) remains the
     irreducible interface boundary (`Stage2_obligations` §3); decoding, token conformance, the
     precise-state condition and the full final-state construction remain NAMED and OPEN.
   * O2 IS CLOSED ONLY AGAINST `Frozen_pmp`'s **MODELLED** MATCHER, not the ratified `pmpCheck`; see
     that file's header for the list of unmodelled PMP features.
   * `Hctx_silent` / `Hchk_nonmem` REMAIN NAMED ANTECEDENTS (consequences of the frozen handler
     schema, which lives in the unmechanized operational layer).  "0 axioms" means nothing is smuggled
     past the interface, NOT that the schema is proved.
   * THEREFORE the honest reading of `stage2_endtoend_v2` is still:
         "every fault candidate satisfying T1's frozen premises admits a trap-free, check-free
          RVWMO-consistent memory KERNEL — consistent on BOTH RVWMO checks, with T1's own relations —
          carrying the same memory projection and read values"
     and NOT "there exists a no-fault EXECUTION".  This file closes a mechanization gap in the
     composition; it does not close the operational gap.

   0 Admitted / 0 axioms (`Print Assumptions stage2_endtoend_v2`).  No existing `.v` file is modified.
   Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.Arith.PeanoNat.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Rlift_mainmodel.
Require Import RestartV.Frozen_mainmodel.
Require Import RestartV.PPO_union.
Require Import RestartV.T1_frozen_refinement.
Require Import RestartV.Adapter_L1_witness.
Require Import RestartV.Obs_final_state.
Require Import RestartV.Ctx_erasure.
Require Import RestartV.Stage2_normal_candidate.
Require Import RestartV.Stage2_state_chain.
Require Import RestartV.Stage2_obligations.
Require Import RestartV.Frozen_pmp.
Import ListNotations.

(* =================================================================================================
   §A.  THE CARRIER-PARAMETERISED WITNESS RELATIONS, AND THEIR IDENTIFICATION WITH `Cn` / `Rn`.

   `Clift_coherence.Cn` and `Rlift_mainmodel.Rn` are stated over ONE hard-wired carrier predicate,
   `survivor x := In x E0 /\ x <> d`.  A Stage-2 chain must move them to further carriers, so we need
   them as functions of the carrier.  `CnC` / `RnC` replace `survivor` by a parameter `C`, and the PPO
   arm of `RnC` now carries `C x /\ C y`.  `CnC_is_Cn` remains definitional; `RnC_is_Rn` instead takes
   an endpoint-carriage proof, supplied for frozen `ppo_wit` by constructor destruction below.
   ================================================================================================= *)

Definition coC (Ev B : Type) (gmoR : Ev -> Ev -> Prop) (isw : Ev -> Prop)
                (tch : Ev -> B -> Prop) (C : Ev -> Prop) (b : B) (w1 w2 : Ev) : Prop :=
  C w1 /\ C w2 /\ isw w1 /\ isw w2 /\ tch w1 b /\ tch w2 b /\ gmoR w1 w2.

Definition frC (Ev B : Type) (gmoR : Ev -> Ev -> Prop) (isw : Ev -> Prop)
                (tch : Ev -> B -> Prop) (rfwR : Ev -> B -> Ev -> Prop)
                (C : Ev -> Prop) (b : B) (r w2 : Ev) : Prop :=
  exists w1, rfwR w1 b r /\ coC Ev B gmoR isw tch C b w1 w2.

(* the PER-LOCATION witness relation at carrier C:  co u fr u rf u po-loc, ALL carrier-restricted *)
Definition CnC (Ev B : Type) (gmoR polocR : Ev -> Ev -> Prop) (isr isw : Ev -> Prop)
                (tch : Ev -> B -> Prop) (rfwR : Ev -> B -> Ev -> Prop)
                (C : Ev -> Prop) (x y : Ev) : Prop :=
  (exists b, coC Ev B gmoR isw tch C b x y) \/
  (exists b, C x /\ C y /\ isr x /\ frC Ev B gmoR isw tch rfwR C b x y) \/
  (exists b, C x /\ C y /\ rfwR x b y) \/
  (polocR x y /\ C x /\ C y).

(* the MAIN-MODEL witness relation at carrier C:  co u fr u rfe u ppo *)
Definition RnC (Ev B Hr : Type) (gmoR : Ev -> Ev -> Prop) (isr isw : Ev -> Prop)
                (tch : Ev -> B -> Prop) (hrt : Ev -> Hr) (rfwR : Ev -> B -> Ev -> Prop)
                (ppowR : Ev -> Ev -> Prop) (C : Ev -> Prop) (x y : Ev) : Prop :=
  (exists b, coC Ev B gmoR isw tch C b x y) \/
  (exists b, C x /\ C y /\ isr x /\ frC Ev B gmoR isw tch rfwR C b x y) \/
  (exists b, C x /\ C y /\ rfwR x b y /\ hrt x <> hrt y) \/
  (C x /\ C y /\ ppowR x y).

(* ---- the identification with the layers' own relations: CONVERTIBILITY, checked by the kernel ---- *)

Theorem CnC_is_Cn :
  forall (Event Byte : Type) (gmo : Event -> Event -> Prop) (is_write is_read : Event -> Prop)
         (touches : Event -> Byte -> Prop) (E0 : list Event)
         (rf : Event -> Byte -> Event -> Prop) (poloc : Event -> Event -> Prop) (d k x y : Event),
    CnC Event Byte gmo poloc is_read is_write touches
        (Clift_coherence.rfw Event Byte rf d k) (Clift_coherence.survivor Event E0 d) x y
    <-> Clift_coherence.Cn Event Byte gmo is_write is_read touches E0 rf poloc d k x y.
Proof. intros. split; intro H; exact H. Qed.

Lemma frozen_ppo_wit_endpoints :
  forall (Event Byte : Type) (po : Event -> Event -> Prop)
         (is_load is_store is_read is_write : Event -> Prop)
         (same_addr addr data ctrl fence : Event -> Event -> Prop)
         (touches : Event -> Byte -> Prop) (rf : Event -> Byte -> Event -> Prop)
         (E0 : list Event) (d k x y : Event),
    Frozen_mainmodel.frozen_ppo_wit Event Byte is_write is_read is_load is_store touches
      same_addr addr data ctrl fence E0 rf po d k x y ->
    Rlift_mainmodel.survivor Event E0 d x /\
    Rlift_mainmodel.survivor Event E0 d y.
Proof.
  intros Event Byte po is_load is_store is_read is_write
         same_addr addr data ctrl fence touches rf E0 d k x y Hppo.
  unfold Frozen_mainmodel.frozen_ppo_wit in Hppo.
  destruct Hppo.
  - split; assumption.
  - split; assumption.
  - split; assumption.
  - split; assumption.
  - split; assumption.
  - split; assumption.
  - split; assumption.
  - unfold PPO_union.r2N, PPO_union.polnw_N in H.
    destruct H as [[_ [_ [_ [_ [_ [Hs_a [Hs_b _]]]]]]] _].
    exact (conj Hs_a Hs_b).
Qed.

Theorem RnC_is_Rn :
  forall (Event Byte Hart : Type) (gmo : Event -> Event -> Prop) (is_write is_read : Event -> Prop)
         (touches : Event -> Byte -> Prop) (hart : Event -> Hart) (E0 : list Event)
         (rf : Event -> Byte -> Event -> Prop) (ppow : Event -> Event -> Prop) (d k : Event),
    (forall x y, ppow x y ->
       Rlift_mainmodel.survivor Event E0 d x /\
       Rlift_mainmodel.survivor Event E0 d y) ->
    forall x y,
      RnC Event Byte Hart gmo is_read is_write touches hart
          (Rlift_mainmodel.rfw Event Byte rf d k) ppow (Rlift_mainmodel.survivor Event E0 d) x y
      <-> Rlift_mainmodel.Rn Event Byte Hart gmo is_write is_read touches hart E0 rf ppow d k x y.
Proof.
  intros Event Byte Hart gmo is_write is_read touches hart E0 rf ppow d k Hends x y.
  unfold RnC, Rlift_mainmodel.Rn. split.
  - intros [Hco | [Hfr | [Hrfe | [_ [_ Hppo]]]]].
    + left. exact Hco.
    + right; left. exact Hfr.
    + right; right; left. exact Hrfe.
    + right; right; right. exact Hppo.
  - intros [Hco | [Hfr | [Hrfe | Hppo]]].
    + left. exact Hco.
    + right; left. exact Hfr.
    + right; right; left. exact Hrfe.
    + right; right; right.
      destruct (Hends x y Hppo) as [Hx Hy].
      exact (conj Hx (conj Hy Hppo)).
Qed.

(* ---- generic acyclicity transfer along a sub-relation ---- *)

Lemma ct_mono_gen : forall (A : Type) (U V : A -> A -> Prop),
  (forall x y, V x y -> U x y) -> forall x y, clos_trans A V x y -> clos_trans A U x y.
Proof.
  intros A U V Hsub x y H. induction H as [x y Hs | x y z _ IH1 _ IH2].
  - apply t_step. apply Hsub. exact Hs.
  - exact (t_trans A U x y z IH1 IH2).
Qed.

Lemma acyclic_sub : forall (A : Type) (U V : A -> A -> Prop),
  (forall x y, V x y -> U x y) ->
  (forall x, ~ clos_trans A U x x) -> forall x, ~ clos_trans A V x x.
Proof.
  intros A U V Hsub Hac x Hc. apply (Hac x). apply (ct_mono_gen A U V Hsub); exact Hc.
Qed.

(* ---- monotonicity in the carrier ---- *)

Lemma coC_mono : forall (Ev B : Type) (gmoR : Ev -> Ev -> Prop) (isw : Ev -> Prop)
                        (tch : Ev -> B -> Prop) (C C' : Ev -> Prop),
  (forall e, C' e -> C e) ->
  forall b w1 w2, coC Ev B gmoR isw tch C' b w1 w2 -> coC Ev B gmoR isw tch C b w1 w2.
Proof.
  intros Ev B gmoR isw tch C C' Hs b w1 w2 H. unfold coC in H.
  destruct H as [I1 [I2 R]]. unfold coC.
  split; [apply Hs; exact I1|]. split; [apply Hs; exact I2|]. exact R.
Qed.

Lemma frC_mono : forall (Ev B : Type) (gmoR : Ev -> Ev -> Prop) (isw : Ev -> Prop)
                        (tch : Ev -> B -> Prop) (rfwR : Ev -> B -> Ev -> Prop) (C C' : Ev -> Prop),
  (forall e, C' e -> C e) ->
  forall b r w2, frC Ev B gmoR isw tch rfwR C' b r w2 -> frC Ev B gmoR isw tch rfwR C b r w2.
Proof.
  intros Ev B gmoR isw tch rfwR C C' Hs b r w2 H. unfold frC in H.
  destruct H as [w1 [Hrf Hco]]. unfold frC. exists w1. split; [exact Hrf|].
  exact (coC_mono Ev B gmoR isw tch C C' Hs b w1 w2 Hco).
Qed.

Lemma CnC_mono : forall (Ev B : Type) (gmoR polocR : Ev -> Ev -> Prop) (isr isw : Ev -> Prop)
                        (tch : Ev -> B -> Prop) (rfwR : Ev -> B -> Ev -> Prop) (C C' : Ev -> Prop),
  (forall e, C' e -> C e) ->
  forall x y, CnC Ev B gmoR polocR isr isw tch rfwR C' x y ->
              CnC Ev B gmoR polocR isr isw tch rfwR C x y.
Proof.
  intros Ev B gmoR polocR isr isw tch rfwR C C' Hs x y H. unfold CnC in H.
  destruct H as [[b Hco] | [ [b [Hx [Hy [Hrx Hfr]]]] | [ [b [Hx [Hy Hrfw]]] | [Hpl [Hx Hy]] ] ]].
  - left. exists b. exact (coC_mono Ev B gmoR isw tch C C' Hs b x y Hco).
  - right; left. exists b.
    split; [apply Hs; exact Hx|]. split; [apply Hs; exact Hy|]. split; [exact Hrx|].
    exact (frC_mono Ev B gmoR isw tch rfwR C C' Hs b x y Hfr).
  - right; right; left. exists b.
    split; [apply Hs; exact Hx|]. split; [apply Hs; exact Hy|]. exact Hrfw.
  - right; right; right.
    split; [exact Hpl|]. split; [apply Hs; exact Hx | apply Hs; exact Hy].
Qed.

Lemma RnC_mono : forall (Ev B Hr : Type) (gmoR : Ev -> Ev -> Prop) (isr isw : Ev -> Prop)
                        (tch : Ev -> B -> Prop) (hrt : Ev -> Hr) (rfwR : Ev -> B -> Ev -> Prop)
                        (ppowR : Ev -> Ev -> Prop) (C C' : Ev -> Prop),
  (forall e, C' e -> C e) ->
  forall x y, RnC Ev B Hr gmoR isr isw tch hrt rfwR ppowR C' x y ->
              RnC Ev B Hr gmoR isr isw tch hrt rfwR ppowR C x y.
Proof.
  intros Ev B Hr gmoR isr isw tch hrt rfwR ppowR C C' Hs x y H. unfold RnC in H.
  destruct H as [[b Hco] | [ [b [Hx [Hy [Hrx Hfr]]]] |
    [ [b [Hx [Hy [Hrfw Hh]]]] | [Hx [Hy Hpp]] ] ]].
  - left. exists b. exact (coC_mono Ev B gmoR isw tch C C' Hs b x y Hco).
  - right; left. exists b.
    split; [apply Hs; exact Hx|]. split; [apply Hs; exact Hy|]. split; [exact Hrx|].
    exact (frC_mono Ev B gmoR isw tch rfwR C C' Hs b x y Hfr).
  - right; right; left. exists b.
    split; [apply Hs; exact Hx|]. split; [apply Hs; exact Hy|]. split; [exact Hrfw | exact Hh].
  - right; right; right.
    split; [apply Hs; exact Hx|]. split; [apply Hs; exact Hy|]. exact Hpp.
Qed.

(* co_max_of is stable under a pointwise-equivalent carrier predicate (needed only to re-index T1's
   final-state observation from `survivor` to `In E_C`; they are the same set by `Adapter_L1_witness`). *)
Lemma co_max_of_ext : forall (Ev B : Type) (gmoR : Ev -> Ev -> Prop) (isw : Ev -> Prop)
                             (tch : Ev -> B -> Prop) (C C' : Ev -> Prop),
  (forall e, C e <-> C' e) ->
  forall b w, Obs_final_state.co_max_of Ev B gmoR isw tch C b w ->
              Obs_final_state.co_max_of Ev B gmoR isw tch C' b w.
Proof.
  intros Ev B gmoR isw tch C C' Hiff b w H. unfold Obs_final_state.co_max_of in H.
  destruct H as [Hw [Ht [Hin Hmax]]]. unfold Obs_final_state.co_max_of.
  split; [exact Hw|]. split; [exact Ht|].
  split; [apply Hiff; exact Hin|].
  intros w' Hin' Hw' Ht'. apply Hmax; [apply Hiff; exact Hin' | exact Hw' | exact Ht'].
Qed.

(* =================================================================================================
   §B.  ERASING A MEMORY-SILENT REGION.

   This is the `Ctx_erasure`-style argument, PROVED here for BOTH RVWMO relations (`Ctx_erasure.v`
   proves it for `Cf` only — defect D3).  The content: every endpoint of every co / fr / rf / rfe /
   po-loc edge is a read, a write, or an event touching a byte; a memory-silent region contains none
   of those; so `CnC` is unchanged.  This argument does NOT apply to PPO: a silent event may still be
   a fence/address/data/control endpoint.  For guarded `RnC` we therefore prove only the
   smaller-carrier-to-larger-carrier inclusion needed to transport acyclicity.  No reverse PPO
   transport is claimed.
   ================================================================================================= *)

Lemma keep_in_EK :
  forall (Ev : Type) (E : list Ev) (Sil : Ev -> Prop) (sil_dec : forall e, {Sil e} + {~ Sil e}) (e : Ev),
    In e E -> ~ Sil e -> In e (Ctx_erasure.EK Ev E Sil sil_dec).
Proof.
  intros Ev E Sil sil_dec e Hin Hns.
  exact (proj2 (Ctx_erasure.In_EK_iff Ev E Sil sil_dec e) (conj Hin Hns)).
Qed.

Lemma keep_write_EK :
  forall (Ev B : Type) (isr isw : Ev -> Prop) (tch : Ev -> B -> Prop) (E : list Ev)
         (Sil : Ev -> Prop) (sil_dec : forall e, {Sil e} + {~ Sil e}),
    (forall e, Sil e -> (~ isr e) /\ (~ isw e) /\ (forall b, ~ tch e b)) ->
    forall e, In e E -> isw e -> In e (Ctx_erasure.EK Ev E Sil sil_dec).
Proof.
  intros Ev B isr isw tch E Sil sil_dec Hsil e Hin Hw.
  apply keep_in_EK; [exact Hin|]. intro Hc.
  destruct (Hsil e Hc) as [_ [Hnw _]]. exact (Hnw Hw).
Qed.

Lemma keep_read_EK :
  forall (Ev B : Type) (isr isw : Ev -> Prop) (tch : Ev -> B -> Prop) (E : list Ev)
         (Sil : Ev -> Prop) (sil_dec : forall e, {Sil e} + {~ Sil e}),
    (forall e, Sil e -> (~ isr e) /\ (~ isw e) /\ (forall b, ~ tch e b)) ->
    forall e, In e E -> isr e -> In e (Ctx_erasure.EK Ev E Sil sil_dec).
Proof.
  intros Ev B isr isw tch E Sil sil_dec Hsil e Hin Hr.
  apply keep_in_EK; [exact Hin|]. intro Hc.
  destruct (Hsil e Hc) as [Hnr _]. exact (Hnr Hr).
Qed.

Lemma keep_touch_EK :
  forall (Ev B : Type) (isr isw : Ev -> Prop) (tch : Ev -> B -> Prop) (E : list Ev)
         (Sil : Ev -> Prop) (sil_dec : forall e, {Sil e} + {~ Sil e}),
    (forall e, Sil e -> (~ isr e) /\ (~ isw e) /\ (forall b, ~ tch e b)) ->
    forall e b, In e E -> tch e b -> In e (Ctx_erasure.EK Ev E Sil sil_dec).
Proof.
  intros Ev B isr isw tch E Sil sil_dec Hsil e b Hin Ht.
  apply keep_in_EK; [exact Hin|]. intro Hc.
  destruct (Hsil e Hc) as [_ [_ Hnt]]. exact (Hnt b Ht).
Qed.

Lemma coC_erase :
  forall (Ev B : Type) (gmoR : Ev -> Ev -> Prop) (isr isw : Ev -> Prop) (tch : Ev -> B -> Prop)
         (E : list Ev) (Sil : Ev -> Prop) (sil_dec : forall e, {Sil e} + {~ Sil e}),
    (forall e, Sil e -> (~ isr e) /\ (~ isw e) /\ (forall b, ~ tch e b)) ->
    forall b w1 w2,
      coC Ev B gmoR isw tch (fun e => In e E) b w1 w2 ->
      coC Ev B gmoR isw tch (fun e => In e (Ctx_erasure.EK Ev E Sil sil_dec)) b w1 w2.
Proof.
  intros Ev B gmoR isr isw tch E Sil sil_dec Hsil b w1 w2 H. unfold coC in H.
  destruct H as [I1 [I2 [W1 [W2 R]]]]. unfold coC.
  split; [exact (keep_write_EK Ev B isr isw tch E Sil sil_dec Hsil w1 I1 W1)|].
  split; [exact (keep_write_EK Ev B isr isw tch E Sil sil_dec Hsil w2 I2 W2)|].
  split; [exact W1|]. split; [exact W2|]. exact R.
Qed.

Lemma CnC_erase_fwd :
  forall (Ev B : Type) (gmoR polocR : Ev -> Ev -> Prop) (isr isw : Ev -> Prop)
         (tch : Ev -> B -> Prop) (rfwR : Ev -> B -> Ev -> Prop)
         (E : list Ev) (Sil : Ev -> Prop) (sil_dec : forall e, {Sil e} + {~ Sil e}),
    (forall e, Sil e -> (~ isr e) /\ (~ isw e) /\ (forall b, ~ tch e b)) ->
    (forall x y, polocR x y -> exists b, tch x b /\ tch y b) ->
    (forall w b r, rfwR w b r -> isw w) ->
    (forall w b r, rfwR w b r -> isr r) ->
    forall x y,
      CnC Ev B gmoR polocR isr isw tch rfwR (fun e => In e E) x y ->
      CnC Ev B gmoR polocR isr isw tch rfwR
          (fun e => In e (Ctx_erasure.EK Ev E Sil sil_dec)) x y.
Proof.
  intros Ev B gmoR polocR isr isw tch rfwR E Sil sil_dec Hsil Hplt Hsrc Htgt x y H.
  unfold CnC in H.
  destruct H as [[b Hco] | [ [b [Hx [Hy [Hrx Hfr]]]] | [ [b [Hx [Hy Hrfw]]] | [Hpl [Hx Hy]] ] ]].
  - left. exists b.
    exact (coC_erase Ev B gmoR isr isw tch E Sil sil_dec Hsil b x y Hco).
  - (* fr: source is a read, target is a write (from the inner coC) *)
    right; left. exists b.
    unfold frC in Hfr. destruct Hfr as [w1 [Hrf1 Hco1]].
    assert (Hy' : In y (Ctx_erasure.EK Ev E Sil sil_dec)).
    { unfold coC in Hco1. destruct Hco1 as [_ [_ [_ [W2 _]]]].
      exact (keep_write_EK Ev B isr isw tch E Sil sil_dec Hsil y Hy W2). }
    split; [exact (keep_read_EK Ev B isr isw tch E Sil sil_dec Hsil x Hx Hrx)|].
    split; [exact Hy'|]. split; [exact Hrx|].
    unfold frC. exists w1. split; [exact Hrf1|].
    exact (coC_erase Ev B gmoR isr isw tch E Sil sil_dec Hsil b w1 y Hco1).
  - (* rf: source is a write, target is a read *)
    right; right; left. exists b.
    split; [exact (keep_write_EK Ev B isr isw tch E Sil sil_dec Hsil x Hx (Hsrc x b y Hrfw))|].
    split; [exact (keep_read_EK Ev B isr isw tch E Sil sil_dec Hsil y Hy (Htgt x b y Hrfw))|].
    exact Hrfw.
  - (* po-loc: both endpoints touch a common byte *)
    right; right; right.
    destruct (Hplt x y Hpl) as [b [Tx Ty]].
    split; [exact Hpl|].
    split; [exact (keep_touch_EK Ev B isr isw tch E Sil sil_dec Hsil x b Hx Tx)
           |exact (keep_touch_EK Ev B isr isw tch E Sil sil_dec Hsil y b Hy Ty)].
Qed.

Theorem CnC_erase_iff :
  forall (Ev B : Type) (gmoR polocR : Ev -> Ev -> Prop) (isr isw : Ev -> Prop)
         (tch : Ev -> B -> Prop) (rfwR : Ev -> B -> Ev -> Prop)
         (E : list Ev) (Sil : Ev -> Prop) (sil_dec : forall e, {Sil e} + {~ Sil e}),
    (forall e, Sil e -> (~ isr e) /\ (~ isw e) /\ (forall b, ~ tch e b)) ->
    (forall x y, polocR x y -> exists b, tch x b /\ tch y b) ->
    (forall w b r, rfwR w b r -> isw w) ->
    (forall w b r, rfwR w b r -> isr r) ->
    forall x y,
      CnC Ev B gmoR polocR isr isw tch rfwR (fun e => In e E) x y <->
      CnC Ev B gmoR polocR isr isw tch rfwR
          (fun e => In e (Ctx_erasure.EK Ev E Sil sil_dec)) x y.
Proof.
  intros Ev B gmoR polocR isr isw tch rfwR E Sil sil_dec Hsil Hplt Hsrc Htgt x y. split.
  - apply (CnC_erase_fwd Ev B gmoR polocR isr isw tch rfwR E Sil sil_dec Hsil Hplt Hsrc Htgt).
  - apply (CnC_mono Ev B gmoR polocR isr isw tch rfwR
             (fun e => In e E) (fun e => In e (Ctx_erasure.EK Ev E Sil sil_dec))).
    exact (Ctx_erasure.EK_sub Ev E Sil sil_dec).
Qed.

Theorem RnC_erase_sub :
  forall (Ev B Hr : Type) (gmoR : Ev -> Ev -> Prop) (isr isw : Ev -> Prop)
         (tch : Ev -> B -> Prop) (hrt : Ev -> Hr) (rfwR : Ev -> B -> Ev -> Prop)
         (ppowR : Ev -> Ev -> Prop)
         (E : list Ev) (Sil : Ev -> Prop) (sil_dec : forall e, {Sil e} + {~ Sil e}),
    forall x y,
      RnC Ev B Hr gmoR isr isw tch hrt rfwR ppowR
          (fun e => In e (Ctx_erasure.EK Ev E Sil sil_dec)) x y ->
      RnC Ev B Hr gmoR isr isw tch hrt rfwR ppowR (fun e => In e E) x y.
Proof.
  intros Ev B Hr gmoR isr isw tch hrt rfwR ppowR E Sil sil_dec x y H.
  exact (RnC_mono Ev B Hr gmoR isr isw tch hrt rfwR ppowR
           (fun e => In e E) (fun e => In e (Ctx_erasure.EK Ev E Sil sil_dec))
           (Ctx_erasure.EK_sub Ev E Sil sil_dec) x y H).
Qed.

(* =================================================================================================
   §C.  REFLECTING BOTH RELATIONS ACROSS LAYER 3's INJECTION `NKeep`.

   Layer 3 lifts the kernel into a new event universe `NEv` with GENERATED check events `NChk l`.
   Every RVWMO predicate of Layer 3 is `False` on `NChk`, so no edge of `CnC`/`RnC` at the normal
   carrier can begin or end at a generated check; every edge therefore REFLECTS to an edge of the
   corresponding relation at `mem_kernel`.  Hence BOTH acyclicity checks transfer.
   ================================================================================================= *)

(* the hart map and the witness ppo, lifted to the normal event universe.  `option Hr` avoids needing
   an inhabitant of `Hr` for the generated checks; externality on the `NKeep` diagonal is unchanged. *)
Definition hart_N (Event Hr Lane : Type) (hrt : Event -> Hr)
                  (n : Stage2_normal_candidate.NEv Event Lane) : option Hr :=
  match n with
  | Stage2_normal_candidate.NKeep _ _ e => Some (hrt e)
  | Stage2_normal_candidate.NChk _ _ _ => None
  end.

Definition ppo_N (Event Lane : Type) (ppowR : Event -> Event -> Prop)
                 (m n : Stage2_normal_candidate.NEv Event Lane) : Prop :=
  match m with
  | Stage2_normal_candidate.NKeep _ _ a =>
      match n with
      | Stage2_normal_candidate.NKeep _ _ b => ppowR a b
      | Stage2_normal_candidate.NChk _ _ _ => False
      end
  | Stage2_normal_candidate.NChk _ _ _ => False
  end.

Lemma CnN_no_NChk_src :
  forall (Event Byte Lane : Type) (gmoR polocR : Event -> Event -> Prop) (isr isw : Event -> Prop)
         (tch : Event -> Byte -> Prop) (rfwR : Event -> Byte -> Event -> Prop)
         (C : Stage2_normal_candidate.NEv Event Lane -> Prop)
         (l : Lane) (n : Stage2_normal_candidate.NEv Event Lane),
    ~ CnC (Stage2_normal_candidate.NEv Event Lane) Byte
        (Stage2_normal_candidate.gmo_N Event Lane gmoR)
        (Stage2_normal_candidate.poloc_N Event Lane polocR)
        (Stage2_normal_candidate.is_read_N Event Lane isr)
        (Stage2_normal_candidate.is_write_N Event Lane isw)
        (Stage2_normal_candidate.touches_N Event Byte Lane tch)
        (Stage2_normal_candidate.rf_N Event Byte Lane rfwR)
        C (Stage2_normal_candidate.NChk Event Lane l) n.
Proof.
  intros Event Byte Lane gmoR polocR isr isw tch rfwR C l n H. unfold CnC in H.
  destruct H as [[b Hco] | [ [b [_ [_ [Hrx _]]]] | [ [b [_ [_ Hrfw]]] | [Hpl _] ] ]].
  - unfold coC in Hco. destruct Hco as [_ [_ [W1 _]]]. exact W1.
  - exact Hrx.
  - exact Hrfw.
  - exact Hpl.
Qed.

Lemma CnN_no_NChk_tgt :
  forall (Event Byte Lane : Type) (gmoR polocR : Event -> Event -> Prop) (isr isw : Event -> Prop)
         (tch : Event -> Byte -> Prop) (rfwR : Event -> Byte -> Event -> Prop)
         (C : Stage2_normal_candidate.NEv Event Lane -> Prop) (a : Event) (l : Lane),
    ~ CnC (Stage2_normal_candidate.NEv Event Lane) Byte
        (Stage2_normal_candidate.gmo_N Event Lane gmoR)
        (Stage2_normal_candidate.poloc_N Event Lane polocR)
        (Stage2_normal_candidate.is_read_N Event Lane isr)
        (Stage2_normal_candidate.is_write_N Event Lane isw)
        (Stage2_normal_candidate.touches_N Event Byte Lane tch)
        (Stage2_normal_candidate.rf_N Event Byte Lane rfwR)
        C (Stage2_normal_candidate.NKeep Event Lane a) (Stage2_normal_candidate.NChk Event Lane l).
Proof.
  intros Event Byte Lane gmoR polocR isr isw tch rfwR C a l H. unfold CnC in H.
  destruct H as [[b Hco] | [ [b [_ [_ [_ Hfr]]]] | [ [b [_ [_ Hrfw]]] | [Hpl _] ] ]].
  - unfold coC in Hco. destruct Hco as [_ [_ [_ [W2 _]]]]. exact W2.
  - unfold frC in Hfr. destruct Hfr as [w1 [_ Hco]].
    unfold coC in Hco. destruct Hco as [_ [_ [_ [W2 _]]]]. exact W2.
  - exact Hrfw.
  - exact Hpl.
Qed.

Lemma RnN_no_NChk_src :
  forall (Event Byte Hr Lane : Type) (gmoR : Event -> Event -> Prop) (isr isw : Event -> Prop)
         (tch : Event -> Byte -> Prop) (hrt : Event -> Hr)
         (rfwR : Event -> Byte -> Event -> Prop) (ppowR : Event -> Event -> Prop)
         (C : Stage2_normal_candidate.NEv Event Lane -> Prop)
         (l : Lane) (n : Stage2_normal_candidate.NEv Event Lane),
    ~ RnC (Stage2_normal_candidate.NEv Event Lane) Byte (option Hr)
        (Stage2_normal_candidate.gmo_N Event Lane gmoR)
        (Stage2_normal_candidate.is_read_N Event Lane isr)
        (Stage2_normal_candidate.is_write_N Event Lane isw)
        (Stage2_normal_candidate.touches_N Event Byte Lane tch)
        (hart_N Event Hr Lane hrt)
        (Stage2_normal_candidate.rf_N Event Byte Lane rfwR)
        (ppo_N Event Lane ppowR)
        C (Stage2_normal_candidate.NChk Event Lane l) n.
Proof.
  intros Event Byte Hr Lane gmoR isr isw tch hrt rfwR ppowR C l n H. unfold RnC in H.
  destruct H as [[b Hco] | [ [b [_ [_ [Hrx _]]]] |
    [ [b [_ [_ [Hrfw _]]]] | [_ [_ Hpp]] ] ]].
  - unfold coC in Hco. destruct Hco as [_ [_ [W1 _]]]. exact W1.
  - exact Hrx.
  - exact Hrfw.
  - exact Hpp.
Qed.

Lemma RnN_no_NChk_tgt :
  forall (Event Byte Hr Lane : Type) (gmoR : Event -> Event -> Prop) (isr isw : Event -> Prop)
         (tch : Event -> Byte -> Prop) (hrt : Event -> Hr)
         (rfwR : Event -> Byte -> Event -> Prop) (ppowR : Event -> Event -> Prop)
         (C : Stage2_normal_candidate.NEv Event Lane -> Prop) (a : Event) (l : Lane),
    ~ RnC (Stage2_normal_candidate.NEv Event Lane) Byte (option Hr)
        (Stage2_normal_candidate.gmo_N Event Lane gmoR)
        (Stage2_normal_candidate.is_read_N Event Lane isr)
        (Stage2_normal_candidate.is_write_N Event Lane isw)
        (Stage2_normal_candidate.touches_N Event Byte Lane tch)
        (hart_N Event Hr Lane hrt)
        (Stage2_normal_candidate.rf_N Event Byte Lane rfwR)
        (ppo_N Event Lane ppowR)
        C (Stage2_normal_candidate.NKeep Event Lane a) (Stage2_normal_candidate.NChk Event Lane l).
Proof.
  intros Event Byte Hr Lane gmoR isr isw tch hrt rfwR ppowR C a l H. unfold RnC in H.
  destruct H as [[b Hco] | [ [b [_ [_ [_ Hfr]]]] |
    [ [b [_ [_ [Hrfw _]]]] | [_ [_ Hpp]] ] ]].
  - unfold coC in Hco. destruct Hco as [_ [_ [_ [W2 _]]]]. exact W2.
  - unfold frC in Hfr. destruct Hfr as [w1 [_ Hco]].
    unfold coC in Hco. destruct Hco as [_ [_ [_ [W2 _]]]]. exact W2.
  - exact Hrfw.
  - exact Hpp.
Qed.

Theorem CnN_reflect :
  forall (Event Byte Lane : Type) (gmoR polocR : Event -> Event -> Prop) (isr isw : Event -> Prop)
         (tch : Event -> Byte -> Prop) (rfwR : Event -> Byte -> Event -> Prop)
         (EK : list Event) (is_chk : Event -> Prop)
         (chk_dec : forall e, {is_chk e} + {~ is_chk e}) (lanes : list Lane)
         (m n : Stage2_normal_candidate.NEv Event Lane),
    CnC (Stage2_normal_candidate.NEv Event Lane) Byte
        (Stage2_normal_candidate.gmo_N Event Lane gmoR)
        (Stage2_normal_candidate.poloc_N Event Lane polocR)
        (Stage2_normal_candidate.is_read_N Event Lane isr)
        (Stage2_normal_candidate.is_write_N Event Lane isw)
        (Stage2_normal_candidate.touches_N Event Byte Lane tch)
        (Stage2_normal_candidate.rf_N Event Byte Lane rfwR)
        (fun z => In z (Stage2_normal_candidate.EN' Event Lane EK is_chk chk_dec lanes)) m n ->
    exists a b, m = Stage2_normal_candidate.NKeep Event Lane a /\
                n = Stage2_normal_candidate.NKeep Event Lane b /\
                CnC Event Byte gmoR polocR isr isw tch rfwR
                    (fun e => In e (Stage2_normal_candidate.mem_kernel Event EK is_chk chk_dec)) a b.
Proof.
  intros Event Byte Lane gmoR polocR isr isw tch rfwR EK is_chk chk_dec lanes m n H.
  destruct m as [a|la];
    [ | exfalso; exact (CnN_no_NChk_src Event Byte Lane gmoR polocR isr isw tch rfwR _ la n H) ].
  destruct n as [b|lb];
    [ | exfalso; exact (CnN_no_NChk_tgt Event Byte Lane gmoR polocR isr isw tch rfwR _ a lb H) ].
  exists a, b. split; [reflexivity|]. split; [reflexivity|].
  unfold CnC in H.
  destruct H as [[bb Hco] | [ [bb [Hx [Hy [Hrx Hfr]]]] | [ [bb [Hx [Hy Hrfw]]] | [Hpl [Hx Hy]] ] ]].
  - left. exists bb. unfold coC in Hco.
    destruct Hco as [I1 [I2 [W1 [W2 [T1 [T2 G]]]]]]. unfold coC.
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes a I1)|].
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes b I2)|].
    split; [exact W1|]. split; [exact W2|]. split; [exact T1|]. split; [exact T2|]. exact G.
  - right; left. exists bb.
    unfold frC in Hfr. destruct Hfr as [w1 [Hrf1 Hco1]].
    destruct w1 as [u|lu]; [ | exfalso; exact Hrf1 ].
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes a Hx)|].
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes b Hy)|].
    split; [exact Hrx|].
    unfold frC. exists u. split; [exact Hrf1|].
    unfold coC in Hco1. destruct Hco1 as [I1 [I2 [W1 [W2 [T1 [T2 G]]]]]]. unfold coC.
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes u I1)|].
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes b I2)|].
    split; [exact W1|]. split; [exact W2|]. split; [exact T1|]. split; [exact T2|]. exact G.
  - right; right; left. exists bb.
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes a Hx)|].
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes b Hy)|].
    exact Hrfw.
  - right; right; right.
    split; [exact Hpl|].
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes a Hx)
           |exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes b Hy)].
Qed.

Theorem RnN_reflect :
  forall (Event Byte Hr Lane : Type) (gmoR : Event -> Event -> Prop) (isr isw : Event -> Prop)
         (tch : Event -> Byte -> Prop) (hrt : Event -> Hr)
         (rfwR : Event -> Byte -> Event -> Prop) (ppowR : Event -> Event -> Prop)
         (EK : list Event) (is_chk : Event -> Prop)
         (chk_dec : forall e, {is_chk e} + {~ is_chk e}) (lanes : list Lane)
         (m n : Stage2_normal_candidate.NEv Event Lane),
    RnC (Stage2_normal_candidate.NEv Event Lane) Byte (option Hr)
        (Stage2_normal_candidate.gmo_N Event Lane gmoR)
        (Stage2_normal_candidate.is_read_N Event Lane isr)
        (Stage2_normal_candidate.is_write_N Event Lane isw)
        (Stage2_normal_candidate.touches_N Event Byte Lane tch)
        (hart_N Event Hr Lane hrt)
        (Stage2_normal_candidate.rf_N Event Byte Lane rfwR)
        (ppo_N Event Lane ppowR)
        (fun z => In z (Stage2_normal_candidate.EN' Event Lane EK is_chk chk_dec lanes)) m n ->
    exists a b, m = Stage2_normal_candidate.NKeep Event Lane a /\
                n = Stage2_normal_candidate.NKeep Event Lane b /\
                RnC Event Byte Hr gmoR isr isw tch hrt rfwR ppowR
                    (fun e => In e (Stage2_normal_candidate.mem_kernel Event EK is_chk chk_dec)) a b.
Proof.
  intros Event Byte Hr Lane gmoR isr isw tch hrt rfwR ppowR EK is_chk chk_dec lanes m n H.
  destruct m as [a|la];
    [ | exfalso; exact (RnN_no_NChk_src Event Byte Hr Lane gmoR isr isw tch hrt rfwR ppowR _ la n H) ].
  destruct n as [b|lb];
    [ | exfalso; exact (RnN_no_NChk_tgt Event Byte Hr Lane gmoR isr isw tch hrt rfwR ppowR _ a lb H) ].
  exists a, b. split; [reflexivity|]. split; [reflexivity|].
  unfold RnC in H.
  destruct H as [[bb Hco] | [ [bb [Hx [Hy [Hrx Hfr]]]] |
    [ [bb [Hx [Hy [Hrfw Hh]]]] | [Hx [Hy Hpp]] ] ]].
  - left. exists bb. unfold coC in Hco.
    destruct Hco as [I1 [I2 [W1 [W2 [T1 [T2 G]]]]]]. unfold coC.
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes a I1)|].
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes b I2)|].
    split; [exact W1|]. split; [exact W2|]. split; [exact T1|]. split; [exact T2|]. exact G.
  - right; left. exists bb.
    unfold frC in Hfr. destruct Hfr as [w1 [Hrf1 Hco1]].
    destruct w1 as [u|lu]; [ | exfalso; exact Hrf1 ].
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes a Hx)|].
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes b Hy)|].
    split; [exact Hrx|].
    unfold frC. exists u. split; [exact Hrf1|].
    unfold coC in Hco1. destruct Hco1 as [I1 [I2 [W1 [W2 [T1 [T2 G]]]]]]. unfold coC.
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes u I1)|].
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes b I2)|].
    split; [exact W1|]. split; [exact W2|]. split; [exact T1|]. split; [exact T2|]. exact G.
  - right; right; left. exists bb.
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes a Hx)|].
    split; [exact (Stage2_normal_candidate.NKeep_in_mem_kernel Event Lane EK is_chk chk_dec lanes b Hy)|].
    split; [exact Hrfw|].
    (* externality on the NKeep diagonal: Some (hrt a) <> Some (hrt b) gives hrt a <> hrt b *)
    intro Heq. apply Hh. simpl. rewrite Heq. reflexivity.
  - right; right; right.
    split.
    + exact (Stage2_normal_candidate.NKeep_in_mem_kernel
               Event Lane EK is_chk chk_dec lanes a Hx).
    + split.
      * exact (Stage2_normal_candidate.NKeep_in_mem_kernel
                 Event Lane EK is_chk chk_dec lanes b Hy).
      * exact Hpp.
Qed.

(* The CONVERSE of the reflection: every kernel edge really IS an edge of the normal candidate on the
   `NKeep` image.  Without this, "Cn_N / Rn_N are acyclic" could be true for the empty reason that the
   normal relations lost their edges.  Together with `CnN_reflect` / `RnN_reflect` this pins the normal
   relations EXACTLY: on the `NKeep` diagonal they ARE the kernel relations. *)

Theorem CnN_inject :
  forall (Event Byte Lane : Type) (gmoR polocR : Event -> Event -> Prop) (isr isw : Event -> Prop)
         (tch : Event -> Byte -> Prop) (rfwR : Event -> Byte -> Event -> Prop)
         (EK : list Event) (is_chk : Event -> Prop)
         (chk_dec : forall e, {is_chk e} + {~ is_chk e}) (lanes : list Lane) (a b : Event),
    CnC Event Byte gmoR polocR isr isw tch rfwR
        (fun e => In e (Stage2_normal_candidate.mem_kernel Event EK is_chk chk_dec)) a b ->
    CnC (Stage2_normal_candidate.NEv Event Lane) Byte
        (Stage2_normal_candidate.gmo_N Event Lane gmoR)
        (Stage2_normal_candidate.poloc_N Event Lane polocR)
        (Stage2_normal_candidate.is_read_N Event Lane isr)
        (Stage2_normal_candidate.is_write_N Event Lane isw)
        (Stage2_normal_candidate.touches_N Event Byte Lane tch)
        (Stage2_normal_candidate.rf_N Event Byte Lane rfwR)
        (fun z => In z (Stage2_normal_candidate.EN' Event Lane EK is_chk chk_dec lanes))
        (Stage2_normal_candidate.NKeep Event Lane a) (Stage2_normal_candidate.NKeep Event Lane b).
Proof.
  intros Event Byte Lane gmoR polocR isr isw tch rfwR EK is_chk chk_dec lanes a b H.
  unfold CnC in H.
  destruct H as [[bb Hco] | [ [bb [Hx [Hy [Hrx Hfr]]]] | [ [bb [Hx [Hy Hrfw]]] | [Hpl [Hx Hy]] ] ]].
  - left. exists bb. unfold coC in Hco.
    destruct Hco as [I1 [I2 [W1 [W2 [T1 [T2 G]]]]]]. unfold coC.
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes a I1)|].
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes b I2)|].
    split; [exact W1|]. split; [exact W2|]. split; [exact T1|]. split; [exact T2|]. exact G.
  - right; left. exists bb.
    unfold frC in Hfr. destruct Hfr as [w1 [Hrf1 Hco1]].
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes a Hx)|].
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes b Hy)|].
    split; [exact Hrx|].
    unfold frC. exists (Stage2_normal_candidate.NKeep Event Lane w1). split; [exact Hrf1|].
    unfold coC in Hco1. destruct Hco1 as [I1 [I2 [W1 [W2 [T1 [T2 G]]]]]]. unfold coC.
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes w1 I1)|].
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes b I2)|].
    split; [exact W1|]. split; [exact W2|]. split; [exact T1|]. split; [exact T2|]. exact G.
  - right; right; left. exists bb.
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes a Hx)|].
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes b Hy)|].
    exact Hrfw.
  - right; right; right.
    split; [exact Hpl|].
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes a Hx)
           |exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes b Hy)].
Qed.

Theorem RnN_inject :
  forall (Event Byte Hr Lane : Type) (gmoR : Event -> Event -> Prop) (isr isw : Event -> Prop)
         (tch : Event -> Byte -> Prop) (hrt : Event -> Hr)
         (rfwR : Event -> Byte -> Event -> Prop) (ppowR : Event -> Event -> Prop)
         (EK : list Event) (is_chk : Event -> Prop)
         (chk_dec : forall e, {is_chk e} + {~ is_chk e}) (lanes : list Lane) (a b : Event),
    RnC Event Byte Hr gmoR isr isw tch hrt rfwR ppowR
        (fun e => In e (Stage2_normal_candidate.mem_kernel Event EK is_chk chk_dec)) a b ->
    RnC (Stage2_normal_candidate.NEv Event Lane) Byte (option Hr)
        (Stage2_normal_candidate.gmo_N Event Lane gmoR)
        (Stage2_normal_candidate.is_read_N Event Lane isr)
        (Stage2_normal_candidate.is_write_N Event Lane isw)
        (Stage2_normal_candidate.touches_N Event Byte Lane tch)
        (hart_N Event Hr Lane hrt)
        (Stage2_normal_candidate.rf_N Event Byte Lane rfwR)
        (ppo_N Event Lane ppowR)
        (fun z => In z (Stage2_normal_candidate.EN' Event Lane EK is_chk chk_dec lanes))
        (Stage2_normal_candidate.NKeep Event Lane a) (Stage2_normal_candidate.NKeep Event Lane b).
Proof.
  intros Event Byte Hr Lane gmoR isr isw tch hrt rfwR ppowR EK is_chk chk_dec lanes a b H.
  unfold RnC in H.
  destruct H as [[bb Hco] | [ [bb [Hx [Hy [Hrx Hfr]]]] |
    [ [bb [Hx [Hy [Hrfw Hh]]]] | [Hx [Hy Hpp]] ] ]].
  - left. exists bb. unfold coC in Hco.
    destruct Hco as [I1 [I2 [W1 [W2 [T1 [T2 G]]]]]]. unfold coC.
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes a I1)|].
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes b I2)|].
    split; [exact W1|]. split; [exact W2|]. split; [exact T1|]. split; [exact T2|]. exact G.
  - right; left. exists bb.
    unfold frC in Hfr. destruct Hfr as [w1 [Hrf1 Hco1]].
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes a Hx)|].
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes b Hy)|].
    split; [exact Hrx|].
    unfold frC. exists (Stage2_normal_candidate.NKeep Event Lane w1). split; [exact Hrf1|].
    unfold coC in Hco1. destruct Hco1 as [I1 [I2 [W1 [W2 [T1 [T2 G]]]]]]. unfold coC.
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes w1 I1)|].
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes b I2)|].
    split; [exact W1|]. split; [exact W2|]. split; [exact T1|]. split; [exact T2|]. exact G.
  - right; right; left. exists bb.
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes a Hx)|].
    split; [exact (Stage2_normal_candidate.mem_kernel_NKeep_in Event Lane EK is_chk chk_dec lanes b Hy)|].
    split; [exact Hrfw|].
    intro Heq. simpl in Heq. injection Heq as Heq. exact (Hh Heq).
  - right; right; right.
    split.
    + exact (Stage2_normal_candidate.mem_kernel_NKeep_in
               Event Lane EK is_chk chk_dec lanes a Hx).
    + split.
      * exact (Stage2_normal_candidate.mem_kernel_NKeep_in
                 Event Lane EK is_chk chk_dec lanes b Hy).
      * exact Hpp.
Qed.

Theorem CnN_acyclic :
  forall (Event Byte Lane : Type) (gmoR polocR : Event -> Event -> Prop) (isr isw : Event -> Prop)
         (tch : Event -> Byte -> Prop) (rfwR : Event -> Byte -> Event -> Prop)
         (EK : list Event) (is_chk : Event -> Prop)
         (chk_dec : forall e, {is_chk e} + {~ is_chk e}) (lanes : list Lane),
    (forall x, ~ clos_trans Event
       (CnC Event Byte gmoR polocR isr isw tch rfwR
          (fun e => In e (Stage2_normal_candidate.mem_kernel Event EK is_chk chk_dec))) x x) ->
    forall n, ~ clos_trans (Stage2_normal_candidate.NEv Event Lane)
       (CnC (Stage2_normal_candidate.NEv Event Lane) Byte
          (Stage2_normal_candidate.gmo_N Event Lane gmoR)
          (Stage2_normal_candidate.poloc_N Event Lane polocR)
          (Stage2_normal_candidate.is_read_N Event Lane isr)
          (Stage2_normal_candidate.is_write_N Event Lane isw)
          (Stage2_normal_candidate.touches_N Event Byte Lane tch)
          (Stage2_normal_candidate.rf_N Event Byte Lane rfwR)
          (fun z => In z (Stage2_normal_candidate.EN' Event Lane EK is_chk chk_dec lanes))) n n.
Proof.
  intros Event Byte Lane gmoR polocR isr isw tch rfwR EK is_chk chk_dec lanes Hacyc.
  assert (Hct : forall m n,
    clos_trans (Stage2_normal_candidate.NEv Event Lane)
      (CnC (Stage2_normal_candidate.NEv Event Lane) Byte
         (Stage2_normal_candidate.gmo_N Event Lane gmoR)
         (Stage2_normal_candidate.poloc_N Event Lane polocR)
         (Stage2_normal_candidate.is_read_N Event Lane isr)
         (Stage2_normal_candidate.is_write_N Event Lane isw)
         (Stage2_normal_candidate.touches_N Event Byte Lane tch)
         (Stage2_normal_candidate.rf_N Event Byte Lane rfwR)
         (fun z => In z (Stage2_normal_candidate.EN' Event Lane EK is_chk chk_dec lanes))) m n ->
    exists a b, m = Stage2_normal_candidate.NKeep Event Lane a /\
                n = Stage2_normal_candidate.NKeep Event Lane b /\
                clos_trans Event
                  (CnC Event Byte gmoR polocR isr isw tch rfwR
                     (fun e => In e (Stage2_normal_candidate.mem_kernel Event EK is_chk chk_dec))) a b).
  { intros m n H. induction H as [m n Hstep | m y n _ IH1 _ IH2].
    - destruct (CnN_reflect Event Byte Lane gmoR polocR isr isw tch rfwR EK is_chk chk_dec lanes m n Hstep)
        as [a [b [Hm [Hn Hc]]]].
      exists a, b. split; [exact Hm|]. split; [exact Hn|]. apply t_step; exact Hc.
    - destruct IH1 as [a [b1 [Hm [Hy1 Hc1]]]].
      destruct IH2 as [b2 [c [Hy2 [Hn Hc2]]]].
      rewrite Hy1 in Hy2. injection Hy2 as Hy2. subst b2.
      exists a, c. split; [exact Hm|]. split; [exact Hn|].
      exact (t_trans Event _ a b1 c Hc1 Hc2). }
  intros n Hcyc.
  destruct (Hct n n Hcyc) as [a [b [Hn1 [Hn2 Hc]]]].
  rewrite Hn1 in Hn2. injection Hn2 as Hn2. subst b. exact (Hacyc a Hc).
Qed.

Theorem RnN_acyclic :
  forall (Event Byte Hr Lane : Type) (gmoR : Event -> Event -> Prop) (isr isw : Event -> Prop)
         (tch : Event -> Byte -> Prop) (hrt : Event -> Hr)
         (rfwR : Event -> Byte -> Event -> Prop) (ppowR : Event -> Event -> Prop)
         (EK : list Event) (is_chk : Event -> Prop)
         (chk_dec : forall e, {is_chk e} + {~ is_chk e}) (lanes : list Lane),
    (forall x, ~ clos_trans Event
       (RnC Event Byte Hr gmoR isr isw tch hrt rfwR ppowR
          (fun e => In e (Stage2_normal_candidate.mem_kernel Event EK is_chk chk_dec))) x x) ->
    forall n, ~ clos_trans (Stage2_normal_candidate.NEv Event Lane)
       (RnC (Stage2_normal_candidate.NEv Event Lane) Byte (option Hr)
          (Stage2_normal_candidate.gmo_N Event Lane gmoR)
          (Stage2_normal_candidate.is_read_N Event Lane isr)
          (Stage2_normal_candidate.is_write_N Event Lane isw)
          (Stage2_normal_candidate.touches_N Event Byte Lane tch)
          (hart_N Event Hr Lane hrt)
          (Stage2_normal_candidate.rf_N Event Byte Lane rfwR)
          (ppo_N Event Lane ppowR)
          (fun z => In z (Stage2_normal_candidate.EN' Event Lane EK is_chk chk_dec lanes))) n n.
Proof.
  intros Event Byte Hr Lane gmoR isr isw tch hrt rfwR ppowR EK is_chk chk_dec lanes Hacyc.
  assert (Hct : forall m n,
    clos_trans (Stage2_normal_candidate.NEv Event Lane)
      (RnC (Stage2_normal_candidate.NEv Event Lane) Byte (option Hr)
         (Stage2_normal_candidate.gmo_N Event Lane gmoR)
         (Stage2_normal_candidate.is_read_N Event Lane isr)
         (Stage2_normal_candidate.is_write_N Event Lane isw)
         (Stage2_normal_candidate.touches_N Event Byte Lane tch)
         (hart_N Event Hr Lane hrt)
         (Stage2_normal_candidate.rf_N Event Byte Lane rfwR)
         (ppo_N Event Lane ppowR)
         (fun z => In z (Stage2_normal_candidate.EN' Event Lane EK is_chk chk_dec lanes))) m n ->
    exists a b, m = Stage2_normal_candidate.NKeep Event Lane a /\
                n = Stage2_normal_candidate.NKeep Event Lane b /\
                clos_trans Event
                  (RnC Event Byte Hr gmoR isr isw tch hrt rfwR ppowR
                     (fun e => In e (Stage2_normal_candidate.mem_kernel Event EK is_chk chk_dec))) a b).
  { intros m n H. induction H as [m n Hstep | m y n _ IH1 _ IH2].
    - destruct (RnN_reflect Event Byte Hr Lane gmoR isr isw tch hrt rfwR ppowR
                  EK is_chk chk_dec lanes m n Hstep) as [a [b [Hm [Hn Hc]]]].
      exists a, b. split; [exact Hm|]. split; [exact Hn|]. apply t_step; exact Hc.
    - destruct IH1 as [a [b1 [Hm [Hy1 Hc1]]]].
      destruct IH2 as [b2 [c [Hy2 [Hn Hc2]]]].
      rewrite Hy1 in Hy2. injection Hy2 as Hy2. subst b2.
      exists a, c. split; [exact Hm|]. split; [exact Hn|].
      exact (t_trans Event _ a b1 c Hc1 Hc2). }
  intros n Hcyc.
  destruct (Hct n n Hcyc) as [a [b [Hn1 [Hn2 Hc]]]].
  rewrite Hn1 in Hn2. injection Hn2 as Hn2. subst b. exact (Hacyc a Hc).
Qed.

(* =================================================================================================
   §D.  THE WIRED CHAIN AND THE HEADLINE.
   ================================================================================================= *)

Section Stage2EndToEnd.

  (* ---- the shared abstract interface (T1's, verbatim, plus Layer 3's) ---- *)
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
  Variables p q k d : Event.                  (* duplicate pair, keeper, deleted *)
  Variable Ctx : Event -> Prop.               (* the trap region *)
  Variable ctx_dec : forall e, {Ctx e} + {~ Ctx e}.
  Variable is_chk : Event -> Prop.            (* the fault run's PMP check events *)
  Variable chk_dec : forall e, {is_chk e} + {~ is_chk e}.
  Variable lane : Event -> Lane.
  Variable is_lane_write : Event -> Prop.
  Variable lanes : list Lane.

  (* ---- T1's hypotheses, in T1's own order ---- *)
  Hypothesis Hirr : forall e, In e E0 -> ~ gmo e e.
  Hypothesis Htr : forall a b c, In a E0 -> In b E0 -> In c E0 -> gmo a b -> gmo b c -> gmo a c.
  Hypothesis Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.
  Hypothesis Hd_in : In d E0.
  Hypothesis Hd_w : is_write d.
  Hypothesis Hk_in : In k E0.
  Hypothesis Hk_w : is_write k.
  Hypothesis Hkd_ne : k <> d.
  Hypothesis Hkeeper : gmo k d.
  Hypothesis Hp_in : In p E0.
  Hypothesis Hq_in : In q E0.
  Hypothesis Hdup : L1_abstract_erasure.DupPair Event Byte Value is_write touches wval p q.
  Hypothesis Hro : L1_abstract_erasure.RO_K Event gmo po p q k.
  Hypothesis Hdpq : d = p \/ d = q.
  Hypothesis Hgamma :
    forall b, L1_abstract_erasure.gamma_adj Event Byte is_write touches E0 gmo b p q.
  Hypothesis Hdupval : forall b, touches d b -> wval k b = wval d b.
  Hypothesis Hrf_is_C4 :
    forall b r w, is_read r -> In r E0 -> rf w b r ->
      L1_abstract_erasure.C4_source Event Byte is_write touches gmo po E0 b r w.
  Hypothesis Hrf_touches : forall w b r, rf w b r -> touches w b.
  Hypothesis Hrw_disjoint : forall e, is_read e -> is_write e -> False.
  Hypothesis Hhart_dk : hart d = hart k.
  Hypothesis Hpo_trans : forall a b c, po a b -> po b c -> po a c.
  Hypothesis Hadj : forall b, touches d b ->
      touches d b /\ touches k b /\
      (forall w, In w E0 -> is_write w -> touches w b -> ~ (gmo k w /\ gmo w d)).
  Hypothesis Hfoot_dk : forall x, touches d x -> touches k x.
  Hypothesis Hpo_twin : forall a b x,
    is_read a -> touches a x -> touches d x -> po a d -> po d b -> po a k /\ po k b.
  Hypothesis Hrf_functional : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.
  Hypothesis Hdup_r12 : forall a b bb,
      po a k -> po k b -> (addr a k \/ data a k) -> rf d bb b ->
      po a d /\ po d b /\ (addr a d \/ data a d).

  (* ---- THE TWO CONSISTENCY ANTECEDENTS.  BOTH ARE THE **FAULT** RUN's, at the FAULT carrier E0.
          Neither mentions any target carrier.  These are T1's own premises, verbatim. ---- *)
  Hypothesis Hfault_perloc :
    forall x, ~ clos_trans Event
      (Clift_coherence.Cf Event Byte gmo is_write is_read touches E0 rf poloc) x x.
  Hypothesis Hfault_main :
    forall x, ~ clos_trans Event
      (Frozen_mainmodel.FRf Event Byte Hart gmo is_write is_read is_load is_store touches
         same_addr addr data ctrl fence hart E0 rf po) x x.

  (* ---- RVWMO typing facts about the interface (the same three `Ctx_erasure` needs) ---- *)
  Hypothesis Hrf_src_write : forall w b r, rf w b r -> is_write w.
  Hypothesis Hrf_tgt_read : forall w b r, rf w b r -> is_read r.
  Hypothesis Hpoloc_touches : forall x y, poloc x y -> exists b, touches x b /\ touches y b.

  (* ---- the two SILENCE antecedents (consequences of the frozen handler schema; NOT proved here) ---- *)
  Hypothesis Hctx_silent :
    forall e, Ctx e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b).
  Hypothesis Hchk_nonmem :
    forall e, is_chk e -> (~ is_read e) /\ (~ is_write e) /\ (forall b, ~ touches e b).

  (* =================================================================================================
     THE CARRIER CHAIN — each definition IS the previous layer's output term.
     ================================================================================================= *)

  Definition E_C : list Event := L1_abstract_erasure.contract_carrier Event eq_ev_dec E0 d.
  Definition rf_C : Event -> Byte -> Event -> Prop :=
    L1_abstract_erasure.rf_retarget Event Byte d k rf.
  Definition E_K : list Event := Ctx_erasure.EK Event E_C Ctx ctx_dec.
  Definition E_MK : list Event := Stage2_normal_candidate.mem_kernel Event E_K is_chk chk_dec.
  Definition E_N : list (Stage2_normal_candidate.NEv Event Lane) :=
    Stage2_normal_candidate.EN' Event Lane E_K is_chk chk_dec lanes.

  (* the witness ppo delivered by T1 (Frozen_mainmodel's, with `ppo_lifts` already discharged) *)
  Definition ppow_C : Event -> Event -> Prop :=
    Frozen_mainmodel.frozen_ppo_wit Event Byte is_write is_read is_load is_store touches
      same_addr addr data ctrl fence E0 rf po d k.

  Lemma ppow_C_endpoints : forall x y, ppow_C x y ->
    Rlift_mainmodel.survivor Event E0 d x /\
    Rlift_mainmodel.survivor Event E0 d y.
  Proof.
    exact (frozen_ppo_wit_endpoints Event Byte po is_load is_store is_read is_write
             same_addr addr data ctrl fence touches rf E0 d k).
  Qed.

  (* T1's OWN relations, carried at each link of the chain.  `Cf` NEVER appears here. *)
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

  (* =================================================================================================
     R1.  `frozen_T1_refinement` IS APPLIED.  `T1_OUT` is that theorem, at this chain's data.
     ================================================================================================= *)

  Definition T1_OUT :=
    T1_frozen_refinement.frozen_T1_refinement
      Event eq_ev_dec Byte Hart Value gmo is_write is_read is_load is_store touches wval
      same_addr addr data ctrl fence hart E0 rf po poloc p q k d
      Hirr Htr Htot Hd_in Hd_w Hk_in Hk_w Hkd_ne Hkeeper Hp_in Hq_in Hdup Hro Hdpq Hgamma Hdupval
      Hrf_is_C4 Hrf_touches Hrw_disjoint Hhart_dk Hpo_trans Hadj Hfoot_dk Hpo_twin Hrf_functional
      Hdup_r12 Hfault_perloc Hfault_main.

  (* =================================================================================================
     R2.  T1's OWN `Cn` / `Rn` land at the contracted carrier `E_C`.
     ================================================================================================= *)

  Lemma in_EC_survivor : forall e, In e E_C -> Clift_coherence.survivor Event E0 d e.
  Proof.
    intros e H.
    exact (proj2 (Adapter_L1_witness.survivor_iff_contract Event eq_ev_dec E0 d e) H).
  Qed.

  Lemma survivor_in_EC : forall e, Clift_coherence.survivor Event E0 d e -> In e E_C.
  Proof.
    intros e H.
    exact (proj1 (Adapter_L1_witness.survivor_iff_contract Event eq_ev_dec E0 d e) H).
  Qed.

  (* THE RELATION WE TRANSPORT **IS** T1's OWN `Cn` / `Rn`.  Not "similar to", not "a version of":
     the same relation, pointwise.  This is what defect D2 was about, and it is stated in the headline
     so that the identification is visible in the PRINTED TYPE, with `Clift_coherence.Cn` and
     `Rlift_mainmodel.Rn` occurring literally. *)

  Theorem Cn_C_is_T1_Cn : forall x y,
    Cn_C x y <-> Clift_coherence.Cn Event Byte gmo is_write is_read touches E0 rf poloc d k x y.
  Proof.
    intros x y. split.
    - intro H.
      exact (proj1 (CnC_is_Cn Event Byte gmo is_write is_read touches E0 rf poloc d k x y)
               (CnC_mono Event Byte gmo poloc is_read is_write touches rf_C
                  (Clift_coherence.survivor Event E0 d) (fun e => In e E_C)
                  in_EC_survivor x y H)).
    - intro H.
      exact (CnC_mono Event Byte gmo poloc is_read is_write touches rf_C
               (fun e => In e E_C) (Clift_coherence.survivor Event E0 d) survivor_in_EC x y
               (proj2 (CnC_is_Cn Event Byte gmo is_write is_read touches E0 rf poloc d k x y) H)).
  Qed.

  Theorem Rn_C_is_T1_Rn : forall x y,
    Rn_C x y <->
    Rlift_mainmodel.Rn Event Byte Hart gmo is_write is_read touches hart E0 rf ppow_C d k x y.
  Proof.
    intros x y. split.
    - intro H.
      exact (proj1 (RnC_is_Rn Event Byte Hart gmo is_write is_read touches hart E0 rf ppow_C d k
                       ppow_C_endpoints x y)
                (RnC_mono Event Byte Hart gmo is_read is_write touches hart rf_C ppow_C
                   (Rlift_mainmodel.survivor Event E0 d) (fun e => In e E_C)
                   in_EC_survivor x y H)).
    - intro H.
      exact (RnC_mono Event Byte Hart gmo is_read is_write touches hart rf_C ppow_C
               (fun e => In e E_C) (Rlift_mainmodel.survivor Event E0 d) survivor_in_EC x y
               (proj2 (RnC_is_Rn Event Byte Hart gmo is_write is_read touches hart E0 rf ppow_C d k
                          ppow_C_endpoints x y) H)).
  Qed.

  Lemma Cn_C_acyclic : forall x, ~ clos_trans Event Cn_C x x.
  Proof.
    destruct T1_OUT as [EN [rfN [_ [_ [Hcn [_ [_ [_ _]]]]]]]].
    apply (acyclic_sub Event
             (Clift_coherence.Cn Event Byte gmo is_write is_read touches E0 rf poloc d k) Cn_C).
    - intros x y H. apply Cn_C_is_T1_Cn. exact H.
    - exact Hcn.
  Qed.

  Lemma Rn_C_acyclic : forall x, ~ clos_trans Event Rn_C x x.
  Proof.
    destruct T1_OUT as [EN [rfN [_ [_ [_ [Hrn [_ [_ _]]]]]]]].
    apply (acyclic_sub Event
             (Rlift_mainmodel.Rn Event Byte Hart gmo is_write is_read touches hart E0 rf ppow_C d k)
             Rn_C).
    - intros x y H. apply Rn_C_is_T1_Rn. exact H.
    - exact Hrn.
  Qed.

  (* =================================================================================================
     R3a.  THE TWO ERASURE HOPS.

     `CnC` still coincides across memory-silent erasure.  Guarded `RnC` is proved only as the
     smaller-carrier subrelation of the larger relation.  This is exactly the direction used below
     for acyclicity and does not pretend that a silent fence/dependency PPO endpoint is retained.
     ================================================================================================= *)

  Lemma rfC_src_write : forall w b r, rf_C w b r -> is_write w.
  Proof.
    intros w b r H. unfold rf_C, L1_abstract_erasure.rf_retarget in H.
    destruct H as [[H1 _] | [_ H2]].
    - exact (Hrf_src_write w b r H1).
    - rewrite H2. exact Hk_w.
  Qed.

  Lemma rfC_tgt_read : forall w b r, rf_C w b r -> is_read r.
  Proof.
    intros w b r H. unfold rf_C, L1_abstract_erasure.rf_retarget in H.
    destruct H as [[H1 _] | [H1 _]].
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

  (* =================================================================================================
     R3b.  BOTH CHECKS ARRIVE AT THE NORMAL CANDIDATE.
     ================================================================================================= *)

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

  (* ANTI-VACUITY at the last hop: on the `NKeep` image the normal relations ARE the kernel relations
     (reflection AND injection), so the acyclicity above is not bought by losing edges. *)

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

  (* =================================================================================================
     THE CARRIERS REALLY NEST
     ================================================================================================= *)

  Lemma E_C_sub_E0 : forall e, In e E_C -> In e E0.
  Proof. exact (L1_abstract_erasure.contract_carrier_sub Event eq_ev_dec E0 d). Qed.

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

  (* =================================================================================================
     T1's OBSERVATION HALF, carried through (this is what makes T1 CONSUMED, not merely cited)
     ================================================================================================= *)

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
    exists w_n. split; [ | exact Hval ].
    apply (co_max_of_ext Event Byte gmo is_write touches
             (Clift_coherence.survivor Event E0 d) (fun e => In e E_C)
             (Adapter_L1_witness.survivor_iff_contract Event eq_ev_dec E0 d) b w_n Hmax).
  Qed.

  (* memory projection along the whole chain: E_C -> E_K -> E_MK -> E_N *)
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

  (* =================================================================================================
     R4a.  O3 AT THE WIRED CHAIN — `Stage2_obligations.O3_reads_keep_values` APPLIED HERE.
     ================================================================================================= *)

  Lemma endtoend_O3 :
    forall r b w, In r E_C -> is_read r -> rf w b r ->
      exists w' : Event,
        Stage2_normal_candidate.rf_N Event Byte Lane rf_C
          (Stage2_normal_candidate.NKeep Event Lane w') b
          (Stage2_normal_candidate.NKeep Event Lane r)
        /\ wval w' b = wval w b.
  Proof.
    intros r b w Hr Hrd Hrf.
    exact (Stage2_obligations.O3_reads_keep_values
             Event eq_ev_dec Byte Value is_write is_read touches wval E0 gmo rf po Lane
             Hrf_is_C4 Hrf_touches p q k d
             (L1_abstract_erasure.Build_gmo_wf Event E0 gmo Hirr Htr Htot)
             Hdup Hro Hdpq Hkd_ne r b w Hr Hrd Hrf).
  Qed.

  (* =================================================================================================
     R4b.  O2 AT THE WIRED LANES — `Frozen_pmp` APPLIED AT THIS CHAIN's `lanes`, and its result used
           as the `pmp_ok_grants` of `Stage2_obligations.O2_closed` (so `grants` is no longer abstract).
     ================================================================================================= *)

  Variable dst VL Kl ram_lo ram_hi : nat.
  Variable lane_index : Lane -> nat.           (* the chain's lanes, as frozen lane indices *)
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

  (* the MODELLED PMP matcher discharges the abstract `grants` of `Stage2_obligations` *)
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

  (* and, unfolded, the concrete statement: every lane of the chain is allowed by the frozen table *)
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

  (* =================================================================================================
     Layer 3's structural candidate, at the wired kernel (kept so this file loses nothing that
     `Stage2_composed` had).
     ================================================================================================= *)

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

  (* =================================================================================================
     HEADLINE.  Read the file header before quoting this.
     ================================================================================================= *)

  Theorem stage2_endtoend_v2 :
    (* --- 1. the carrier chain nests, and the last link is an IFF --- *)
    ((forall e, In e E_C -> In e E0)
     /\ (forall e, In e E_K -> In e E_C)
     /\ (forall e, In e E_MK -> In e E_K)
     /\ (forall e, In (Stage2_normal_candidate.NKeep Event Lane e) E_N <-> In e E_MK)
     /\ (forall e, In e E_K -> ~ Ctx e))
    (* --- 2. R1: T1 IS CONSUMED — its L1-consistency and BOTH observation halves, at the chain --- *)
    /\ L1_abstract_erasure.L1_consistent Event Byte is_write is_read touches gmo po E_C rf_C
    /\ (forall r b w, In r E_C -> is_read r -> rf w b r ->
          exists w', rf_C w' b r /\ wval w' b = wval w b)
    /\ (forall b w_f,
          Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E0) b w_f ->
          exists w_n,
            Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E_C) b w_n
            /\ wval w_f b = wval w_n b)
    (* --- 3. R2: THE TRANSPORTED RELATIONS **ARE** T1's OWN `Cn` / `Rn` (pointwise identity, with
             `Clift_coherence.Cn` and `Rlift_mainmodel.Rn` occurring literally — this is defect D2),
             and their acyclicity is DERIVED from the FAULT-run antecedents, NOT assumed. --- *)
    /\ (forall x y, Cn_C x y <->
          Clift_coherence.Cn Event Byte gmo is_write is_read touches E0 rf poloc d k x y)
    /\ (forall x y, Rn_C x y <->
          Rlift_mainmodel.Rn Event Byte Hart gmo is_write is_read touches hart E0 rf ppow_C d k x y)
    /\ (forall x y, ppow_C x y ->
          Rlift_mainmodel.survivor Event E0 d x /\
          Rlift_mainmodel.survivor Event E0 d y)
    /\ (forall x, ~ clos_trans Event Cn_C x x)
    /\ (forall x, ~ clos_trans Event Rn_C x x)
    (* --- 4. R3: Cn is unchanged; guarded Rn is the target-to-source subrelation needed for
             acyclicity.  No reverse PPO transport is claimed from memory silence. --- *)
    /\ (forall x y, Cn_C x y <-> Cn_K x y)
    /\ (forall x y, Rn_K x y -> Rn_C x y)
    /\ (forall x y, Cn_K x y <-> Cn_MK x y)
    /\ (forall x y, Rn_MK x y -> Rn_K x y)
    (* --- 5. R3: BOTH RVWMO CHECKS ARRIVE AT THE NORMAL CANDIDATE, and the normal relations are
             EXACTLY the kernel relations on the `NKeep` image (so acyclicity is not vacuous) --- *)
    /\ (forall a b, Cn_N (Stage2_normal_candidate.NKeep Event Lane a)
                         (Stage2_normal_candidate.NKeep Event Lane b) <-> Cn_MK a b)
    /\ (forall a b, Rn_N (Stage2_normal_candidate.NKeep Event Lane a)
                         (Stage2_normal_candidate.NKeep Event Lane b) <-> Rn_MK a b)
    /\ (forall n, ~ clos_trans (Stage2_normal_candidate.NEv Event Lane) Cn_N n n)
    /\ (forall n, ~ clos_trans (Stage2_normal_candidate.NEv Event Lane) Rn_N n n)
    (* --- 6. the byte-wise memory projection is preserved along the WHOLE chain --- *)
    /\ (forall b w,
          Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e E_C) b w
          <-> Obs_final_state.co_max_of (Stage2_normal_candidate.NEv Event Lane) Byte
                (Stage2_normal_candidate.gmo_N Event Lane gmo)
                (Stage2_normal_candidate.is_write_N Event Lane is_write)
                (Stage2_normal_candidate.touches_N Event Byte Lane touches)
                (fun n => In n E_N) b (Stage2_normal_candidate.NKeep Event Lane w))
    (* --- 7. Layer 3's STRUCTURAL candidate (NOT the operational `Cand_N`) --- *)
    /\ Stage2_normal_candidate.Cand_N_struct Event Lane E_K lane is_lane_write is_chk chk_dec lanes
    (* --- 8. R4: O3 at the wired chain --- *)
    /\ (forall r b w, In r E_C -> is_read r -> rf w b r ->
          exists w' : Event,
            Stage2_normal_candidate.rf_N Event Byte Lane rf_C
              (Stage2_normal_candidate.NKeep Event Lane w') b
              (Stage2_normal_candidate.NKeep Event Lane r)
            /\ wval w' b = wval w b)
    (* --- 9. R4: non-vacuous O2 lane/index/event wiring, then the modelled PMP conclusions --- *)
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
      split; [exact E_K_sub_E_C|].
      split; [exact E_MK_sub_E_K|].
      split; [exact E_N_NKeep_iff | exact E_K_trap_free]. }
    split; [exact endtoend_L1_consistent|].
    split; [exact endtoend_read_values|].
    split; [exact endtoend_final_state|].
    split; [exact Cn_C_is_T1_Cn|].
    split; [exact Rn_C_is_T1_Rn|].
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

End Stage2EndToEnd.

(* =================================================================================================
   END.  Relative to `Stage2_composed.v`:
     * D1 REPAIRED — `frozen_T1_refinement` is applied (`T1_OUT`), and every acyclicity/observation
       conjunct of the headline is derived by destructing it.
     * D2 REPAIRED — the transported relations are T1's own `Cn` / `Rn`; frozen PPO endpoint carriage
       is proved constructor-by-constructor.
     * D3 REPAIRED — guarded target main-model relations are carried as subrelations, the exact
       direction needed for acyclicity; no false reverse silent-erasure claim remains.
     * R4 — O2 has explicit finite-lane/index coverage and event-byte footprint wiring; O3 is
       instantiated at the chain's own carrier and reads-from relation.
   What is NOT established is listed in the file header: no operational execution, no `StateWF`, no
   `Cand_N`, O1 still the interface boundary, and `Hctx_silent` / `Hchk_nonmem` still named antecedents.
   0 Admitted / 0 axioms.
   ================================================================================================= *)
