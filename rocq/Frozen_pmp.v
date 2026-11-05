(* Frozen_pmp.v — RESTART-V: closing obligation O2 against a MODELLED PMP matcher.

   ===================================================================================================
   WHY THIS FILE EXISTS — IT IS A CORRECTION OF AN EARLIER OVERCLAIM.  READ THIS FIRST.
   ===================================================================================================
   `Stage2_obligations.v` §1 claimed O2 "CLOSED".  A review found that what it actually proved is
   much weaker than the obligation, in two specific ways, and both of them are hidden by ONE
   abstraction: the file carried

       Variable   grants  : Entry -> Lane -> Prop.
       Hypothesis pmp_ok_grants : forall l, grants pmp_ok l.
       Definition check_succeeds (t : Idx -> Entry) (l : Lane) : Prop := grants (t dsg) l.

   and then `O2_closed : forall t l, check_succeeds (pmp_repaired t) l` follows from
   `L3_handler.pmp_update_designated` plus the hypothesis, with no PMP content anywhere.  Namely:

     (a) IT ASSUMED AWAY THE REAL CONTENT.  `grants` is an uninterpreted predicate.  Nothing in that
         file decodes a NAPOT range, nothing checks that an 8-byte access is FULLY contained in the
         matched region, nothing performs the priority scan, and nothing implements U-mode
         default-deny.  The whole of "the PMP check succeeds" was `pmp_ok_grants`, assumed.

     (b) IT CONTAINED A GENUINE GAP — IT COLLAPSED ALL LANES ONTO THE DESIGNATED ENTRY.
         `check_succeeds t l := grants (t dsg) l` makes EVERY lane's check consult the designated
         (repaired) entry `dsg`.  That is not what the frozen configuration does.  In the frozen
         configuration the repaired entry 0 is an 8-byte NAPOT region covering EXACTLY lane K; a lane
         i <> K does not intersect it at all and is permitted by a DIFFERENT, UNCHANGED BACKGROUND
         ENTRY.  The old model therefore proved the wrong lanes' checks for the wrong reason.

   Additionally, the real matcher's failure mode is not "this entry does not apply, try the next one":
   under RISC-V PMP the FIRST entry that matches AT ALL — fully OR PARTIALLY — decides, and a PARTIAL
   match is an ACCESS FAULT, not a skip.  An entry-local `grants` predicate cannot express that, so the
   old formulation could not even state the hazard it needed to rule out.

   ===================================================================================================
   WHAT THIS FILE DOES INSTEAD
   ===================================================================================================
   It replaces the abstract `grants` predicate with a MODELLED matcher over half-open address ranges:

     * NAPOT-style regions (an entry is `OFF`, or covers a half-open interval `[elo, ehi)`);
     * FULL-CONTAINMENT semantics — an access `[lo,hi)` fully inside the region is `FullM`, an access
       that overlaps but is not contained is `PartM`, and a disjoint access is `NoM`;
     * the PRIORITY SCAN in which the first entry with a non-`NoM` result DECIDES — full OR partial;
     * U-mode DEFAULT-DENY — with no matching entry at all, a U-mode access is denied (M-mode
       proceeds).

   Against that matcher it proves, for the frozen two-entry table:

     * entry 0 = the REPAIRED entry, an 8-byte NAPOT region over exactly lane K, W = 1;
     * entry 1 = the BACKGROUND entry, UNCHANGED by the handler, covering every lane, W = 1;

   the headline `frozen_pmp_lane_checks_succeed`: EVERY lane's U-mode 8-byte store is allowed.

   THE `i = K` / `i <> K` SPLIT, STATED EXPLICITLY — this is the structure the old abstraction hid:

     * `i = K`   : the access is FULLY contained in the repaired entry, so the scan STOPS at entry 0,
                   which grants W.  Lane K is the lane the handler repaired.
     * `i <> K`  : lane i does not intersect the repaired entry AT ALL — this is `repaired_NoM_off_lane`,
                   and it rests on `lanes_disjoint`, the 8-byte-alignment fact that lanes are pairwise
                   disjoint.  So entry 0 returns `NoM` (NOT `PartM`, which would be a FAULT), the scan
                   FALLS THROUGH to entry 1, and lane i is permitted by the UNCHANGED BACKGROUND ENTRY
                   — not by the repaired one.  The alignment/disjointness step is exactly the content
                   that `grants` assumed away.

   NEITHER CASE REACHES THE `None` BRANCH of `allows`, so U-mode default-deny is never needed here.
   It is modelled anyway, and exercised by the tripwire `unmatched_U_denied`, so that the deny
   behaviour is present in the model rather than merely absent.

   NON-VACUITY.  Two tripwire lemmas show the model can actually say "no":
     * `partial_overlap_is_denied` — a PARTIAL overlap really does deny (it does not skip the entry);
     * `unmatched_U_denied`        — an unmatched U-mode access really is denied.
   Without these, an `allows` predicate that were accidentally trivial would prove the headline for
   free.

   ===================================================================================================
   WHAT IS STILL **NOT** MODELLED — DO NOT OVERSELL THIS FILE
   ===================================================================================================
   This is a FROZEN-TABLE MODEL of PMP matching, written here.  It is NOT the ratified RISC-V
   `pmpCheck`, and it is not derived from, checked against, or connected to the Sail source.  In
   particular the following are NOT modelled:

     * WARL / read-back effects of `pmpWriteCfg` — a value written to `pmpcfg` need not read back
       unchanged; an unsupported mode may be forced to `OFF`.  This file simply POSITS that entry 0
       holds a NAPOT region with W = 1 after the repair.
     * ENTRY LOCKING — the `L` bit, and the rule that a locked TOR entry also blocks writes to the
       preceding `pmpaddr`.  A locked entry 0 would make the repair a no-op; nothing here rules it out.
     * PA-WIDTH TRIMMING of `pmpaddr` — addresses are `nat` here, unbounded and untrimmed.
     * TOR and NA4 modes — only an `OFF` / interval-covering (`MNapot`) distinction exists here, and
       `MNapot` is modelled as an ARBITRARY half-open interval, so the NAPOT power-of-two /
       alignment ENCODING of `pmpaddr` is not modelled either.
     * OTHER PERMISSIONS AND ACCESS KINDS — only the `W` bit and 8-byte U-mode STORES.  `R`, `X`,
       instruction fetch, loads, AMOs and their sub-cases are absent.
     * MORE THAN TWO ENTRIES — the frozen table is exactly `[entry_repaired; entry_background]`.  Real
       PMP has up to 64 entries with the full priority order among them.
     * THE M-MODE PATHS — `PrivM` exists in the model only so that default-deny can be stated for
       `PrivU`; `mseccfg`/MML/MMWP, and M-mode's behaviour on matched locked entries, are absent.

   Bridging this predicate to the SOURCE-GENERATED `pmpCheck` remains the open step, and it is not
   attempted here.

   ---------------------------------------------------------------------------------------------------
   HONEST STATUS LINE:
     O2 is now closed against a MODELLED frozen PMP matcher, NOT against the ratified model.
   ---------------------------------------------------------------------------------------------------

   0 Admitted / 0 axioms (`Print Assumptions frozen_pmp_lane_checks_succeed`).
   No existing `.v` file is modified.  Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* =================================================================================================
   1.  THE MODEL — privilege, entry, match result, matcher, priority scan, permission.
   ================================================================================================= *)

Inductive Priv := PrivM | PrivU.

(* Only the distinction the frozen table needs: an entry is OFF, or it covers an interval.
   NOTE (see header): `MNapot` is an ARBITRARY half-open interval; the power-of-two NAPOT ENCODING
   of `pmpaddr` is NOT modelled.  TOR and NA4 are absent. *)
Inductive Mode := MOff | MNapot.

Record Entry := { emode : Mode; elo : nat; ehi : nat; ew : bool }.
(* An `MNapot` entry covers the half-open range [elo, ehi).  `ew` is the W permission bit; R, X and
   the L (lock) bit are NOT modelled. *)

Inductive MatchR := NoM | PartM | FullM.

(* The access is [lo, hi).  FULL CONTAINMENT is required for a `FullM`; anything that overlaps
   without being contained is `PartM`, which the scan below treats as DECIDING (and `allows` then
   denies) — a partial match is an access fault, NOT "skip this entry". *)
Definition matchr (e : Entry) (lo hi : nat) : MatchR :=
  match emode e with
  | MOff => NoM
  | MNapot =>
      if orb (Nat.leb hi (elo e)) (Nat.leb (ehi e) lo) then NoM          (* disjoint *)
      else if andb (Nat.leb (elo e) lo) (Nat.leb hi (ehi e)) then FullM  (* fully contained *)
      else PartM                                                        (* overlap, not contained *)
  end.

(* The PRIORITY SCAN: the FIRST entry with a non-`NoM` result decides — full OR partial. *)
Fixpoint scan (es : list Entry) (lo hi : nat) : option Entry :=
  match es with
  | nil => None
  | e :: r => match matchr e lo hi with NoM => scan r lo hi | _ => Some e end
  end.

(* A U-mode store is allowed iff the DECIDING entry fully matches AND grants W.  With no match at
   all, U-mode is DENIED (M-mode would proceed) — U-mode default-deny. *)
Definition allows (es : list Entry) (lo hi : nat) (p : Priv) : Prop :=
  match scan es lo hi with
  | Some e => matchr e lo hi = FullM /\ ew e = true
  | None   => p = PrivM
  end.

(* =================================================================================================
   2.  GENERIC MATCHER FACTS (introduction rules, so later proofs never depend on `simpl` behaviour)
   ================================================================================================= *)

Lemma matchr_NoM_intro : forall e lo hi,
  emode e = MNapot -> (hi <= elo e \/ ehi e <= lo) -> matchr e lo hi = NoM.
Proof.
  intros e lo hi Hm H. unfold matchr. rewrite Hm.
  destruct H as [H|H].
  - rewrite (proj2 (Nat.leb_le _ _) H). reflexivity.
  - rewrite (proj2 (Nat.leb_le _ _) H). rewrite orb_true_r. reflexivity.
Qed.

Lemma matchr_FullM_intro : forall e lo hi,
  emode e = MNapot -> lo < hi -> elo e <= lo -> hi <= ehi e -> matchr e lo hi = FullM.
Proof.
  intros e lo hi Hm Hlt H1 H2. unfold matchr. rewrite Hm.
  assert (E1 : Nat.leb hi (elo e) = false) by (apply Nat.leb_gt; lia).
  assert (E2 : Nat.leb (ehi e) lo = false) by (apply Nat.leb_gt; lia).
  rewrite E1, E2. simpl.
  rewrite (proj2 (Nat.leb_le _ _) H1), (proj2 (Nat.leb_le _ _) H2). reflexivity.
Qed.

Lemma scan_cons_NoM : forall e es lo hi,
  matchr e lo hi = NoM -> scan (e :: es) lo hi = scan es lo hi.
Proof. intros e es lo hi H. simpl. rewrite H. reflexivity. Qed.

Lemma scan_cons_hit : forall e es lo hi,
  matchr e lo hi <> NoM -> scan (e :: es) lo hi = Some e.
Proof.
  intros e es lo hi H. simpl.
  destruct (matchr e lo hi); [ exfalso; apply H; reflexivity | reflexivity | reflexivity ].
Qed.

(* =================================================================================================
   3.  TRIPWIRES — the model is NOT vacuous: it can say "no".
   ================================================================================================= *)

(* A PARTIAL overlap really does DENY.  This is the hazard the old entry-local `grants` predicate
   could not even state: partially overlapping an entry is an access fault, not a skip. *)
Lemma partial_overlap_is_denied :
  forall e lo hi p, matchr e lo hi = PartM -> ~ allows (e :: nil) lo hi p.
Proof.
  intros e lo hi p Hm Hall. unfold allows in Hall.
  rewrite (scan_cons_hit e nil lo hi) in Hall by (rewrite Hm; discriminate).
  destruct Hall as [Hf _]. rewrite Hm in Hf. discriminate.
Qed.

(* U-MODE DEFAULT-DENY: an unmatched U-mode access really is denied. *)
Lemma unmatched_U_denied : forall lo hi, ~ allows nil lo hi PrivU.
Proof. intros lo hi H. unfold allows in H. simpl in H. discriminate H. Qed.

(* ... and the M-mode counterpart, recorded only to show the `None` branch is not uniformly false
   (so `unmatched_U_denied` is a real discrimination, not a degenerate one). *)
Lemma unmatched_M_proceeds : allows nil 0 8 PrivM.
Proof. unfold allows. simpl. reflexivity. Qed.

(* =================================================================================================
   4.  THE FROZEN TABLE AND THE HEADLINE.
   ================================================================================================= *)

Section FrozenTable.

  Variable dst : nat.            (* base of the vector-store footprint *)
  Variable VL K : nat.           (* vector length; the repaired lane *)
  Hypothesis K_lt : K < VL.
  Variable ram_lo ram_hi : nat.  (* the background region *)

  (* Lanes are 8 bytes and 8-byte aligned: lane i occupies [dst + 8*i, dst + 8*i + 8). *)
  Definition lane_lo (i : nat) : nat := dst + 8 * i.
  Definition lane_hi (i : nat) : nat := dst + 8 * i + 8.

  (* Entry 0 — DESIGNATED, REPAIRED.  An 8-byte NAPOT region over exactly lane K, W = 1.
     (Frozen scope: `pmpaddr0 = (dst + K*8) >> 2`, `pmpcfg0` low byte `0x1B` = NAPOT|R|W.) *)
  Definition entry_repaired : Entry :=
    {| emode := MNapot; elo := lane_lo K; ehi := lane_hi K; ew := true |}.

  (* Entry 1 — BACKGROUND, UNCHANGED by the handler.  Covers the whole data region, W = 1.
     (Frozen scope: `0x1F` = NAPOT|R|W|X.) *)
  Definition entry_background : Entry :=
    {| emode := MNapot; elo := ram_lo; ehi := ram_hi; ew := true |}.

  Definition repaired_table : list Entry := entry_repaired :: entry_background :: nil.

  (* Registered frozen-scope fact about the background region: it covers every lane. *)
  Hypothesis bg_covers : forall i, i < VL -> ram_lo <= lane_lo i /\ lane_hi i <= ram_hi.

  (* --------------------------------------------------------------------------------------------
     RESULT 1.  THE ALIGNMENT / DISJOINTNESS LEMMA — the content the abstract `grants` hid.
     Distinct 8-byte-aligned lanes are pairwise DISJOINT.  Without this, a lane i <> K could
     PARTIALLY overlap the repaired entry, which under the real matcher is an access FAULT.
     -------------------------------------------------------------------------------------------- *)
  Lemma lanes_disjoint : forall i j, i <> j -> lane_hi i <= lane_lo j \/ lane_hi j <= lane_lo i.
  Proof.
    intros i j Hij. unfold lane_hi, lane_lo.
    assert (H : i < j \/ j < i) by lia.
    destruct H as [H|H]; [ left | right ]; lia.
  Qed.

  (* --------------------------------------------------------------------------------------------
     RESULT 2.  Entry 0 does NOT partially match any other lane — it is `NoM`, so no spurious fault
     and the scan may legitimately fall through to the background entry.
     -------------------------------------------------------------------------------------------- *)
  Lemma repaired_NoM_off_lane :
    forall i, i <> K -> matchr entry_repaired (lane_lo i) (lane_hi i) = NoM.
  Proof.
    intros i Hi. apply matchr_NoM_intro; [ reflexivity | ].
    exact (lanes_disjoint i K Hi).
  Qed.

  (* --------------------------------------------------------------------------------------------
     RESULT 3.  Entry 0 FULLY matches lane K (full 8-byte containment, not mere overlap).
     -------------------------------------------------------------------------------------------- *)
  Lemma repaired_FullM_at_K : matchr entry_repaired (lane_lo K) (lane_hi K) = FullM.
  Proof.
    apply matchr_FullM_intro.
    - reflexivity.
    - unfold lane_lo, lane_hi. lia.
    - unfold entry_repaired. simpl. lia.
    - unfold entry_repaired. simpl. lia.
  Qed.

  (* --------------------------------------------------------------------------------------------
     RESULT 4.  The BACKGROUND entry fully matches every lane.
     -------------------------------------------------------------------------------------------- *)
  Lemma background_FullM :
    forall i, i < VL -> matchr entry_background (lane_lo i) (lane_hi i) = FullM.
  Proof.
    intros i Hi. destruct (bg_covers i Hi) as [Hlo Hhi].
    apply matchr_FullM_intro.
    - reflexivity.
    - unfold lane_lo, lane_hi. lia.
    - unfold entry_background. simpl. exact Hlo.
    - unfold entry_background. simpl. exact Hhi.
  Qed.

  (* The two scan outcomes, made explicit so the headline's case split is readable. *)

  Lemma scan_at_K : scan repaired_table (lane_lo K) (lane_hi K) = Some entry_repaired.
  Proof.
    unfold repaired_table. apply scan_cons_hit.
    rewrite repaired_FullM_at_K. discriminate.
  Qed.

  Lemma scan_off_lane : forall i, i <> K -> i < VL ->
    scan repaired_table (lane_lo i) (lane_hi i) = Some entry_background.
  Proof.
    intros i Hne Hi. unfold repaired_table.
    rewrite (scan_cons_NoM entry_repaired _ _ _ (repaired_NoM_off_lane i Hne)).
    apply scan_cons_hit. rewrite (background_FullM i Hi). discriminate.
  Qed.

  (* ============================== HEADLINE (O2, MODELLED) ==============================
     Every lane's U-mode 8-byte store is ALLOWED by the frozen repaired table.

     THE SPLIT:
       * i = K   : the scan STOPS at entry 0 — full containment — and entry 0 grants W.
       * i <> K  : entry 0 returns `NoM` (RESULT 2, via the alignment/disjointness lemma), so the
                   scan FALLS THROUGH to entry 1, the UNCHANGED BACKGROUND entry, which fully
                   matches and grants W.  The non-faulting lanes are permitted by the background
                   entry, NOT by the repaired one.

     NEITHER CASE REACHES THE `None` BRANCH of `allows`, so U-mode default-deny is never needed
     here; it is modelled and exercised separately by `unmatched_U_denied` above. *)
  Theorem frozen_pmp_lane_checks_succeed :
    forall i, i < VL -> allows repaired_table (lane_lo i) (lane_hi i) PrivU.
  Proof.
    intros i Hi. unfold allows.
    destruct (Nat.eq_dec i K) as [Heq|Hne].
    - (* i = K : decided by the REPAIRED entry *)
      subst i. rewrite scan_at_K.
      split; [ exact repaired_FullM_at_K | reflexivity ].
    - (* i <> K : decided by the UNCHANGED BACKGROUND entry *)
      rewrite (scan_off_lane i Hne Hi).
      split; [ exact (background_FullM i Hi) | reflexivity ].
  Qed.

  (* An auditor's corollary: for i <> K the DECIDING entry is literally `entry_background`, i.e. the
     entry the handler did NOT touch.  Stated so that the printed type exhibits the correction to the
     old `check_succeeds t l := grants (t dsg) l`, which consulted the designated entry for EVERY
     lane. *)
  Corollary off_lane_decided_by_background :
    forall i, i <> K -> i < VL ->
      scan repaired_table (lane_lo i) (lane_hi i) = Some entry_background.
  Proof. exact scan_off_lane. Qed.

  (* And the dual: lane K IS decided by the repaired entry. *)
  Corollary K_lane_decided_by_repaired :
    scan repaired_table (lane_lo K) (lane_hi K) = Some entry_repaired.
  Proof. exact scan_at_K. Qed.

End FrozenTable.

(* =================================================================================================
   END.  O2 is now closed against a MODELLED frozen PMP matcher, NOT against the ratified model.
   The open step is the bridge from `allows` / `matchr` / `scan` to the SOURCE-GENERATED `pmpCheck`,
   together with everything enumerated in the header as NOT modelled (WARL/read-back, L-bit and
   TOR-successor locking, PA-width trimming, TOR/NA4, other permissions and access kinds, more than
   two entries, the M-mode paths).
   0 Admitted / 0 axioms.
   ================================================================================================= *)
