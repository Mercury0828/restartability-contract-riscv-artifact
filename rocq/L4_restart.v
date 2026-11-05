(* L4_restart.v — RESTART-V M4, Layer 4 (partial): packaging each restart reading into L1's reduced
   RestartOrder interface.

   HONESTY NOTE (revised after round-11 blind audit). This does NOT mechanize the resumed-vector
   memory-order fidelity risk (D-a's #1 residual risk). It has no execution semantics: no token, PC,
   instance identity, provenance, fence, dependency, or concrete `po` generator. Each "reading" is a
   RECORD whose fields carry the reading's model facts. Continuation carries a two-sided po-envelope
   field and a coherence-direction field (either direction admissible — inherent to that reading).
   Re-execution (round-11 F6 fix) now DERIVES its keeper: its fields are po p q + both-writes +
   same-location, and `gmo p q` follows from the named CoWW axiom + co ⊆ gmo, not postulated. The
   theorem then
   repackages those fields into L1's reduced interface (`po_envelope /\ exists k, is_keeper k`), and
   is conditional on `Continuation \/ Reexecution` (neither is shown inhabited for an execution). The
   reduced `po_envelope` is the EXTERNAL-only, outgoing direction (round-12 audit FATAL fix: it must
   exclude the duplicates p,q themselves, else `po p q` + a universal envelope forces `po q q` and no
   strict-po execution inhabits the record); it does not cover incoming envelope, fence/dependency
   preservation, provenance, or r12 endpoint support.

   What it genuinely shows: IF a reading provides its RO conclusions, they fit L1's interface, so L1's
   erasure kernel does not privilege one reading over the other at the interface level. Deriving those
   conclusions from concrete execution semantics is the remaining work. Self-contained; 0 Admitted /
   0 axioms (Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Import ListNotations.

Section Restart.

  Variable Event : Type.
  Variable gmo : Event -> Event -> Prop.
  Variable po  : Event -> Event -> Prop.

  (* The two lane writes of the interrupted vector instruction. *)
  Variables p q : Event.

  (* The keeper / po-envelope facts the L1 erasure kernel consumes (mirrors L1's RO_K record). *)
  Definition is_keeper (k : Event) : Prop :=
    (k = p /\ gmo p q) \/ (k = q /\ gmo q p).

  (* po-envelope over EXTERNAL events only (e distinct from both duplicates).
     Round-12 audit FATAL fix: the previous unrestricted `forall e, po p e <-> po q e` quantified
     over e = q, giving `po p q <-> po q q`; combined with the Re-execution field `po p q` that
     forces `po q q`, contradicting strict-po irreflexivity — the record was uninhabitable. The
     envelope only ever meant the duplicates share their EXTERNAL neighborhood, so it must exclude
     p and q themselves. *)
  Definition po_envelope : Prop := forall e, e <> p -> e <> q -> (po p e <-> po q e).

  (* ---- Continuation reading ---- *)
  (* p,q are events of ONE logical token; they share the token's external po-neighborhood (RO-E by
     construction), and coherence between them may go either way; the keeper is whichever is
     gmo-earlier. *)
  Record Continuation : Prop := {
    cont_po_env : forall e, e <> p -> e <> q -> (po p e <-> po q e);  (* shared EXTERNAL envelope *)
    cont_co     : gmo p q \/ gmo q p                   (* either coherence direction admissible *)
  }.

  Theorem continuation_gives_RO :
    Continuation -> po_envelope /\ exists k, is_keeper k.
  Proof.
    intros [Henv Hco]. split.
    - exact Henv.
    - destruct Hco as [Gpq|Gqp].
      + exists p. left. split; [reflexivity | exact Gpq].
      + exists q. right. split; [reflexivity | exact Gqp].
  Qed.

  (* ---- Re-execution reading ---- *)
  (* p (first attempt) and q (replay) are distinct dynamic instances at the same program position:
     they share the external po-envelope (same PC), and the first is coherence-before the replay.

     Round-11 audit F6 fix: instead of ASSUMING `gmo p q` outright, we now DERIVE first-before-replay
     from named RVWMO primitives. p and q are two writes to the same location, p po-before q; the
     per-location coherence axiom CoWW orders same-location writes by po (co p q); and co ⊆ gmo (C1,
     mechanized in L2_consistency). So `gmo p q` is a consequence, not a bare postulate. The named
     primitives (is_write, same_loc, po p q, coWW, co_sub_gmo) are the honest interface. *)
  Variable is_write : Event -> Prop.
  Variable same_loc : Event -> Event -> Prop.
  Variable co : Event -> Event -> Prop.
  Hypothesis co_sub_gmo : forall x y, co x y -> gmo x y.          (* C1: co ⊆ gmo *)
  Hypothesis coWW :                                                 (* per-location CoWW *)
    forall x y, is_write x -> is_write y -> same_loc x y -> po x y -> co x y.

  Record Reexecution : Prop := {
    reex_po_env : forall e, e <> p -> e <> q -> (po p e <-> po q e);  (* shared EXTERNAL envelope *)
    reex_wp     : is_write p;                            (* p is a store *)
    reex_wq     : is_write q;                            (* q (replay) is a store *)
    reex_loc    : same_loc p q;                          (* same target location *)
    reex_po     : po p q                                 (* first is program-order before replay *)
  }.

  (* first-before-replay is DERIVED: gmo p q from CoWW + co ⊆ gmo. *)
  Lemma reexecution_first : Reexecution -> gmo p q.
  Proof.
    intros [Henv Hwp Hwq Hloc Hpo].
    apply co_sub_gmo. apply (coWW p q Hwp Hwq Hloc Hpo).
  Qed.

  Theorem reexecution_gives_RO :
    Reexecution -> po_envelope /\ exists k, is_keeper k.
  Proof.
    intros HR. split.
    - exact (reex_po_env HR).
    - exists p. left. split; [reflexivity | exact (reexecution_first HR)].
  Qed.

  (* Both readings yield the same interface, so any theorem proved against (po_envelope /\
     admissible keeper) — i.e. the L1 erasure kernel — holds under either reading. *)
  Theorem both_readings_give_RO :
    (Continuation \/ Reexecution) -> po_envelope /\ exists k, is_keeper k.
  Proof.
    intros [HC|HR]; [apply continuation_gives_RO; exact HC
                    | apply reexecution_gives_RO; exact HR].
  Qed.

End Restart.
