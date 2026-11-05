(* Token_model.v — RESTART-V M4: the po-twin (D4) and dup_r12 (D6) properties DERIVED from the
   trap/replay token structure, in the CORRECT re-execution orientation.

   ORIENTATION (self-check #1 CG-1 fix — the coherence gate). The two dynamic occurrences of the one
   static faulting vector store are:
       k = the FIRST attempt (the provisional lane write, at the store's normal program position);
       d = the REPLAY (issued after the trap is repaired, from `vstart`).
   In program order the first attempt comes first — `po k d` — and strictly between them lies only
   the TRAP REGION (the M-mode handler + `mret`): an event is `in_trap` iff it is po-between k and d.
   Because the two writes overlap and `po k d`, CoWW puts the first attempt coherence-EARLIER, so the
   KEEPER is `k` (coherence-earlier, `gmo k d`) and the ERASED duplicate is `d` (the replay,
   coherence-later). This matches `T1_frozen_refinement.keeper_before : gmo k d` exactly.

   [Why the previous orientation was vacuous: labelling `d` the first/provisional write and keeping
    the replay `k` forces `po d k`, hence (CoWW) `gmo d k`, contradicting the capstone's `gmo k d`.
    No real re-execution inhabits that. The keeper is the first attempt, not the replay.]

   `po_twin_derived` is the RO-adapter theorem for D4. Under `po k d` the OUTGOING half (`po d b ->
   po k b`) is immediate by transitivity; the INCOMING half (`po a d -> po a k`) holds for a NORMAL
   U-mode access `a` of the store's data footprint — such an access is never a trap-region (M-mode
   handler) event, so it cannot sit po-between the first attempt and the replay. That last fact is a
   scope-register commitment (the handler does not read/write the U-mode store's data footprint), not
   a memory-model assumption. `dup_r12_derived` (D6) is likewise re-derived for `po k d`.

   Self-contained; 0 Admitted / 0 axioms. Coq 8.15. *)

Require Import Coq.Lists.List.
Import ListNotations.

Section TokenModel.

  Variable Event : Type.
  Variable Byte : Type.
  Variable po : Event -> Event -> Prop.
  Variable is_read is_write : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.

  (* po is a strict total order on the relevant (same-hart) events. For cross-hart pairs po is empty,
     so every po-premise below is false and the twin/r12 facts hold vacuously — the content is same-hart. *)
  Hypothesis po_irrefl : forall a, ~ po a a.
  Hypothesis po_trans  : forall a b c, po a b -> po b c -> po a c.

  Variables d k : Event.
  Hypothesis pkd : po k d.            (* the FIRST attempt (keeper k) is program-order before the REPLAY (deleted d) *)
  Hypothesis k_is_write : is_write k.
  Hypothesis rw_disjoint : forall e, is_read e -> is_write e -> False.

  (* the trap region: events strictly po-between the first attempt (k) and the replay (d) — the
     M-mode handler + mret. *)
  Definition in_trap (e : Event) : Prop := po k e /\ po e d.

  (* linearity we need, LOCALIZED (audit CG-1.5): only events that are already po-before the replay d
     are po-comparable to k. Since `po e d` and `po k d` place e, k on d's hart, and po is a strict
     total order PER HART, comparability holds — WITHOUT asserting the (false) cross-hart totality
     `forall e, e<>k -> po e k \/ po k e`. Events on other harts are never po-before d, so are not
     constrained here. *)
  Hypothesis po_total_before_d : forall e, e <> k -> po e d -> po e k \/ po k e.

  (* SCOPE-REGISTER commitment: a U-mode access of the store's data footprint is a NORMAL access,
     never a trap-region (M-mode handler) event. The handler repairs a PMP entry; it does not touch
     the faulting store's U-mode data footprint. *)
  Hypothesis footprint_read_not_in_trap :
    forall a x, is_read a -> touches a x -> touches d x -> ~ in_trap a.

  (* ---- D4: the po-twin RO-adapter theorem (re-execution orientation) ---- *)
  (* For a NORMAL footprint read `a` po-before the replay `d`, and any `b` po-after `d`: the first
     attempt (keeper k) occupies the same po-cut — `po a k` and `po k b`. This is exactly the shape
     the r2/polnw lift consumes (its endpoints are reads that touch the store byte `x`). *)
  Theorem po_twin_derived :
    forall a b x, is_read a -> touches a x -> touches d x -> po a d -> po d b -> po a k /\ po k b.
  Proof.
    intros a b x Rda Tax Tdx Pad Pdb. split.
    - (* po a k : a is a footprint read ⇒ not in trap ⇒ (a≠k, totality) po a k *)
      assert (Hnt : ~ in_trap a) by (apply (footprint_read_not_in_trap a x); assumption).
      assert (Hak : a <> k). { intro E. subst a. exact (rw_disjoint k Rda k_is_write). }
      destruct (po_total_before_d a Hak Pad) as [Pak | Pka].
      + exact Pak.
      + exfalso. apply Hnt. split; [exact Pka | exact Pad].
    - (* po k b : k <po d <po b *)
      apply (po_trans k d b pkd Pdb).
  Qed.

  (* Sanity: the first attempt k is itself never in the trap region (it is the region's lower endpoint). *)
  Lemma k_not_in_trap : ~ in_trap k.
  Proof. intros [Hkk _]. exact (po_irrefl k Hkk). Qed.

  (* ---- D6: the dup_r12 hypothesis DERIVED from the token structure (re-execution orientation) ---- *)
  (* The first attempt k and replay d are two dynamic occurrences of ONE static store instruction, so
     they carry the SAME syntactic dependencies. The load `b` that reads from the deleted replay `d`
     is po-after it (an observer read of the completed store's value — a scope commitment; same-hart
     internal reads-from is program-order-later). From those token facts + `po k d`, the r12
     intermediate-transfer fact (keeper's r12 role transfers to the deleted duplicate) follows. *)
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable addr data : Event -> Event -> Prop.
  (* d,k are occurrences of the same static instruction ⇒ identical syntactic deps *)
  Hypothesis same_static_deps :
    forall e, (addr e k -> addr e d) /\ (data e k -> data e d).
  (* reader-after-replay, the INTERNAL-rf (rfi) case only (audit CG-1.4 + GPT Pro item 2). The `po k b`
     guard forces `b` onto `k`'s hart; since `d` and `k` share a hart (hart_dk in the capstone), `b`
     reads `d` INTERNALLY (rfi), and rfi forces the write program-order-before the read — so `po d b`.
     This is a consequence of per-hart po-totality + the RVWMO per-location coherence axiom C3
     (`b po d` would close the C3 cycle `d →rfi b →po d`), and of the frozen scope fact that observer
     footprint accesses are excluded (β_frozen), so any reader of `d` is a same-hart suffix access.
     It is DELIBERATELY NOT the global `rf d bb b -> po d b`, which is FALSE for a cross-hart external
     reader `rfe d bb b` (empty po); such readers never satisfy `po k b` and raise no dup_r12 obligation.
     (A fuller development would derive this as a C3 consistency lemma rather than list it here; recorded
     as available cleanup — GPT Pro confirms frozen-soundness either way.) *)
  Hypothesis reader_after_d : forall bb b, po k b -> rf d bb b -> po d b.

  (* exactly the `dup_r12` hypothesis shape used by PPO_union / T1_frozen. *)
  Theorem dup_r12_derived :
    forall a b bb, po a k -> po k b -> (addr a k \/ data a k) -> rf d bb b ->
      po a d /\ po d b /\ (addr a d \/ data a d).
  Proof.
    intros a b bb Hak Hkb Hdep Hrf.
    split; [ apply (po_trans a k d Hak pkd) |].                      (* po a d: a <po k <po d *)
    split; [ apply (reader_after_d bb b Hkb Hrf) |].                 (* po d b: b (on k's hart) observes replay d *)
    destruct Hdep as [Ha|Ha]; destruct (same_static_deps a) as [Fa Fd].
    - left;  apply Fa; exact Ha.
    - right; apply Fd; exact Ha.
  Qed.

End TokenModel.
