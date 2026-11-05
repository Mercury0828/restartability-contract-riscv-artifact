(* L2_gamma.v — RESTART-V M4, Layer 2 (partial): gamma_D => gamma_adj.

   HONESTY NOTE (revised after round-11 blind audit). This machine-checks ONLY the conditional
   implication gamma_D => gamma_adj under the listed model interfaces (r1, po-comparability, the
   two-sided po-envelope, gmo_wf). It does NOT prove gamma_D is STRICTLY stronger than gamma_adj (no
   countermodel), does NOT prove gamma_adj is necessary/minimal, and does NOT treat gamma_E (which is
   not even defined here). So gamma_adj is a SUFFICIENT erasure condition that gamma_D implies; the
   sharper "gamma_adj is the true/necessary semantic core, gamma_D/gamma_E strictly conservative"
   claim (P8) is design prose, not what this theorem establishes. Establishing gamma_E => gamma_D and
   strictness is future work.

   The proof is the "same-hart bracketing" argument: under gamma_D every other write to the byte is
   on h0; the RO-E po-envelope + po-comparability place it po-before both duplicates or po-after
   both; r1 (subset of gmo) turns that into gmo-before-both or gmo-after-both; hence none lies
   strictly between them, which is exactly gamma_adj.

   Self-contained; 0 Admitted / 0 axioms (checked by Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Import ListNotations.

Section L2_gamma.

  Variable Event : Type.
  Variable Byte  : Type.
  Variable is_write : Event -> Prop.
  Variable touches  : Event -> Byte -> Prop.

  Variable E0  : list Event.
  Variable gmo : Event -> Event -> Prop.

  Record gmo_wf : Prop := {
    gmo_irrefl : forall e, In e E0 -> ~ gmo e e;
    gmo_trans  : forall a b c, In a E0 -> In b E0 -> In c E0 ->
                               gmo a b -> gmo b c -> gmo a c
  }.

  Variable po : Event -> Event -> Prop.

  (* Two harts; the faulting hart h0 owns the duplicates. *)
  Variable Hart : Type.
  Variable hart : Event -> Hart.
  Variable h0   : Hart.

  (* Same definitions of between / gamma_adj as L1. *)
  Definition between (b : Byte) (p q z : Event) : Prop :=
    is_write z /\ touches z b /\ z <> p /\ z <> q /\
    ((gmo p z /\ gmo z q) \/ (gmo q z /\ gmo z p)).

  Definition gamma_adj (b : Byte) (p q : Event) : Prop :=
    ~ exists z, In z E0 /\ between b p q z.

  (* gamma_D at the duplicated byte b: every write touching b is on h0. *)
  Definition gamma_D_at (b : Byte) : Prop :=
    forall w, In w E0 -> is_write w -> touches w b -> hart w = h0.

  Theorem gamma_D_implies_gamma_adj :
    gmo_wf ->
    forall b p q,
      In p E0 -> In q E0 ->
      is_write p -> touches p b -> is_write q -> touches q b ->
      (* r1 (subset of gmo): a write po-before a write to the same byte is gmo-before it. *)
      (forall a c, In a E0 -> In c E0 -> is_write a -> is_write c ->
                   touches a b -> touches c b -> po a c -> gmo a c) ->
      (* po-comparability: any other h0 write to b is po-before or po-after p. *)
      (forall z, In z E0 -> is_write z -> touches z b -> hart z = h0 ->
                 z <> p -> z <> q -> po z p \/ po p z) ->
      (* RO-E po-envelope: p and q share their po relation to every event. *)
      (forall z, (po z p <-> po z q) /\ (po p z <-> po q z)) ->
      gamma_D_at b ->
      gamma_adj b p q.
  Proof.
    intros Hwf b p q Hp Hq Wp Tp Wq Tq Hr1 Hcomp Henv HgD.
    destruct Hwf as [Hirr Htr].
    (* a gmo 2-cycle is impossible *)
    assert (Hcyc : forall a c, In a E0 -> In c E0 -> gmo a c -> gmo c a -> False).
    { intros a c Ia Ic Hac Hca. apply (Hirr a Ia). apply (Htr a c a Ia Ic Ia Hac Hca). }
    intros [z [Inz Hbtw]].
    destruct Hbtw as [Wz [Tz [Nzp [Nzq Hdisj]]]].
    assert (Hhz : hart z = h0) by (apply HgD; assumption).
    (* bracket: z is gmo-before both duplicates, or gmo-after both. *)
    assert (Hbr : (gmo z p /\ gmo z q) \/ (gmo p z /\ gmo q z)).
    { destruct (Hcomp z Inz Wz Tz Hhz Nzp Nzq) as [Pzp|Ppz].
      - left. split.
        + apply (Hr1 z p Inz Hp Wz Wp Tz Tp Pzp).
        + apply (Hr1 z q Inz Hq Wz Wq Tz Tq).
          apply (proj1 (proj1 (Henv z))). exact Pzp.
      - right. split.
        + apply (Hr1 p z Hp Inz Wp Wz Tp Tz Ppz).
        + apply (Hr1 q z Hq Inz Wq Wz Tq Tz).
          apply (proj1 (proj2 (Henv z))). exact Ppz. }
    (* contradiction: "between" needs before-one/after-other, bracket gives before-both/after-both *)
    destruct Hbr as [[Bzp Bzq]|[Bpz Bqz]]; destruct Hdisj as [[Hpz Hzq]|[Hqz Hzp]].
    - exact (Hcyc z p Inz Hp Bzp Hpz).
    - exact (Hcyc z q Inz Hq Bzq Hqz).
    - exact (Hcyc z q Inz Hq Hzq Bqz).
    - exact (Hcyc z p Inz Hp Hzp Bpz).
  Qed.

End L2_gamma.
