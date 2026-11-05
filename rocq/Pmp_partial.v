(* Pmp_partial.v — RESTART-V: the partial-match rule of the PMP model, on any table.

   Under RISC-V PMP the highest-priority entry that matches ANY byte of an access decides it, and the
   access fails unless that entry contains the WHOLE access. `Frozen_pmp.allows` implements this rule
   (`scan` stops at the first entry with a non-`NoM` result). This file states the rule for an
   arbitrary table and exercises it on the example of the privileged specification:

     * `allows_iff_deciding_full`: a U-mode store is allowed iff the first entry that matches any of
       its bytes contains all of them and grants W;
     * `spec_example_denied`: an 8-byte store to [0x8, 0x10) under a table whose first entry covers
       [0xC, 0x10) with W set and whose second entry covers everything with W set is DENIED, although
       every byte of it is writable under some entry;
     * `frozen_lanes_never_partial`: in the frozen two-entry table, no lane is partially matched by
       the repaired entry, which is what lets every lane pass (`Frozen_pmp.frozen_pmp_lane_checks_succeed`).

   0 Admitted / 0 axioms. Modifies no existing .v file. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import RestartV.Frozen_pmp.
Import ListNotations.

(* the deciding entry of an access: the first entry that matches any of its bytes *)
Theorem allows_iff_deciding_full : forall es lo hi,
    allows es lo hi PrivU <->
    exists e, scan es lo hi = Some e /\ matchr e lo hi = FullM /\ ew e = true.
Proof.
  intros es lo hi. unfold allows. split.
  - destruct (scan es lo hi) as [e |]; [intros [H1 H2]; exists e; auto | discriminate].
  - intros [e [Hs [H1 H2]]]. rewrite Hs. auto.
Qed.

(* a partial match by the deciding entry denies the access, whatever entries follow *)
Theorem partial_deciding_denies : forall e es lo hi,
    matchr e lo hi = PartM -> ~ allows (e :: es) lo hi PrivU.
Proof.
  intros e es lo hi Hm Hall. unfold allows in Hall.
  rewrite (scan_cons_hit e es lo hi) in Hall by (rewrite Hm; discriminate).
  destruct Hall as [Hf _]. rewrite Hm in Hf. discriminate.
Qed.

(* the example of the privileged specification *)
Definition spec_top : Entry := {| emode := MNapot; elo := 12; ehi := 16; ew := true |}.
Definition spec_bg  : Entry := {| emode := MNapot; elo := 0; ehi := 4096; ew := true |}.

Theorem spec_example_denied : ~ allows [spec_top; spec_bg] 8 16 PrivU.
Proof.
  apply partial_deciding_denies. reflexivity.
Qed.

(* every byte of that store is writable under some entry, so the denial is due to partial match *)
Theorem spec_example_bytes_writable : forall a, 8 <= a < 16 ->
    allows [spec_top; spec_bg] a (S a) PrivU.
Proof.
  intros a Ha. unfold allows.
  destruct (Nat.lt_ge_cases a 12) as [Hlt | Hge].
  - assert (Hn : matchr spec_top a (S a) = NoM)
      by (apply matchr_NoM_intro; [reflexivity | left; simpl; lia]).
    rewrite (scan_cons_NoM _ _ _ _ Hn).
    assert (Hf : matchr spec_bg a (S a) = FullM)
      by (apply matchr_FullM_intro; [reflexivity | lia | simpl; lia | simpl; lia]).
    rewrite (scan_cons_hit spec_bg [] a (S a)) by (rewrite Hf; discriminate).
    split; [exact Hf | reflexivity].
  - assert (Hf : matchr spec_top a (S a) = FullM)
      by (apply matchr_FullM_intro; [reflexivity | lia | simpl; lia | simpl; lia]).
    rewrite (scan_cons_hit spec_top _ a (S a)) by (rewrite Hf; discriminate).
    split; [exact Hf | reflexivity].
Qed.

(* in the frozen table the repaired entry never partially matches a lane *)
Theorem frozen_lanes_never_partial : forall dst K i,
    matchr (entry_repaired dst K) (lane_lo dst i) (lane_hi dst i) <> PartM.
Proof.
  intros dst K i.
  destruct (Nat.eq_dec i K) as [E | N].
  - rewrite E. rewrite (repaired_FullM_at_K dst (S K) K (Nat.lt_succ_diag_r K)). discriminate.
  - rewrite (repaired_NoM_off_lane dst (S K) K (Nat.lt_succ_diag_r K) i N). discriminate.
Qed.
