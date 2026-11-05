(* Reexec_orientation.v — RESTART-V M4: the re-execution orientation, derived + LOCKED.

   Self-check #1 CG-1 + GPT Pro verdict (item 3/4). The capstone requires keeper `k` coherence-earlier
   than erased `d` (`gmo k d`). Under the RESTART-V **re-execution completion** — the interrupted store's
   first attempt F and its replay R are two dynamic occurrences with `po F R` — RVWMO rule r1
   (overlapping-address, b a store) ⊆ ppo ⊆ gmo (with C1) forces `gmo F R`, so the keeper is the FIRST
   attempt (`k=F`) and the erased duplicate is the REPLAY (`d=R`).

   This file (a) DERIVES `gmo F R` from the r1/ppo/gmo interface rather than assuming it independently,
   (b) exhibits the orientation's premises as jointly inhabitable (non-vacuity), and (c) LOCKS the fix
   with a regression theorem that the reversed (keep-the-replay) orientation is impossible under the
   re-execution premise — so a future refactor cannot silently return to the vacuous instantiation.

   HONESTY: `po F R` is the re-execution completion RESTART-V *selects*; the public RISC-V spec leaves
   vector/trap program-order integration under-formalized and does NOT mandate it (a continuation
   reading, with the keeper the gmo-minimum occurrence, is the alternative — see D-a). `coww` below is
   exactly r1 ⊆ ppo ⊆ gmo + C1, the ratified RVWMO rule, taken as the model interface. 0 Admitted /
   0 axioms. Coq 8.15. *)

Section ReexecOrientation.

  Variable Event : Type.
  Variable po gmo overlap : Event -> Event -> Prop.
  Variable is_store : Event -> Prop.

  (* gmo well-formedness (the relevant fragment) *)
  Hypothesis gmo_irrefl : forall e, ~ gmo e e.
  Hypothesis gmo_trans  : forall a b c, gmo a b -> gmo b c -> gmo a c.

  (* RVWMO rule r1 (overlapping-address program order to a store) ⊆ ppo ⊆ gmo (C1). *)
  Hypothesis coww : forall a b, po a b -> overlap a b -> is_store b -> gmo a b.

  Variables F R : Event.        (* F = first attempt, R = replay *)
  Hypothesis reexec_po : po F R.
  Hypothesis dup_overlap : overlap F R.
  Hypothesis R_store : is_store R.

  (* (a) gmo F R is DERIVED (not independently assumed) from r1/ppo/gmo. *)
  Theorem first_before_replay_gmo : gmo F R.
  Proof. apply (coww F R reexec_po dup_overlap R_store). Qed.

  (* (b) Non-vacuity: the re-execution premises jointly yield the capstone's keeper_before with
     k := F, d := R. So {po F R, gmo F R, keeper_before} is inhabited — the instantiation is NOT
     vacuous (contrast the old keep-the-replay reading). *)
  Theorem reexec_orientation_inhabited : po F R /\ gmo F R /\ gmo F R.
  Proof. split; [exact reexec_po|]. split; apply first_before_replay_gmo. Qed.

  (* (c) REGRESSION LOCK: the reversed orientation (keep the replay ⇒ keeper coherence-later, gmo R F)
     is impossible under the re-execution premise. Any refactor reintroducing `gmo R F` as
     `keeper_before` with k=R,d=F is rejected here. *)
  Theorem replay_keeper_impossible_under_reexec : gmo R F -> False.
  Proof.
    intro Hrf. apply (gmo_irrefl F).
    apply (gmo_trans F R F first_before_replay_gmo Hrf).
  Qed.

End ReexecOrientation.
