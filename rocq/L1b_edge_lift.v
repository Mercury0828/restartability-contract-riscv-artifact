(* L1b_edge_lift.v — RESTART-V M4: the mathematical crux of the erasure edge-lift (Clift/Rlift).

   This is GENUINE T1 content, not spec transcription. The top-level `witness_acyclic_if_edges_lift`
   (Top_T1_skeleton) leaves the edge-lift hypotheses Rlift/Clift unproven; those say every no-fault-
   witness coherence edge is supported by a fault-run path with the same retained endpoints. The two
   witness edge kinds among survivors are:

     - co edges (write w1 <co w2, both surviving): lift is INCLUSION — witness co among survivors is
       literally a fault-run co edge, since erasure removes only the deleted duplicate d and does not
       change gmo among the survivors. (`co_survivor_is_fault`.)

     - fr edges (read r reads the keeper k after retargeting, and k <co w2): in the FAULT run r reads
       the DELETED duplicate d, so the supporting fault edge needs d <co w2, i.e. gmo d w2. This does
       NOT hold for arbitrary d,k — it holds precisely because d and k are ADJACENT duplicates at the
       byte (gamma_adj): no b-touching write lies strictly gmo-between them. That adjacency is exactly
       what forces gmo d w2 from gmo k w2. (`fr_lift_core`.)

   So this file mechanizes why gamma_adj is a SUFFICIENT erasure condition at the edge level: it is a
   hypothesis that discharges the hard orientation of the fr lift (only the k..d no-between direction
   of `adj` is actually used below; adjacency is not claimed necessary/minimal — e.g. if gmo d w2
   already holds the lift succeeds regardless). The rf-retargeting bookkeeping (that r reads k in the
   witness and d in the fault run) is L1's `rf_retarget`; here we prove the coherence-order crux the
   lift rests on. Self-contained; 0 Admitted / 0 axioms (Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Import ListNotations.

Section EdgeLift.

  Variable Event : Type.
  Variable eq_ev : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte : Type.
  Variable gmo : Event -> Event -> Prop.
  Variable is_write : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable E0 : list Event.

  Record gmo_wf : Prop := {
    g_irr : forall e, In e E0 -> ~ gmo e e;
    g_tr  : forall a b c, In a E0 -> In b E0 -> In c E0 -> gmo a b -> gmo b c -> gmo a c;
    g_tot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a
  }.

  (* Coherence at byte b on carrier E0: two b-touching writes ordered by gmo. *)
  Definition coF (b : Byte) (w1 w2 : Event) : Prop :=
    In w1 E0 /\ In w2 E0 /\ is_write w1 /\ is_write w2 /\
    touches w1 b /\ touches w2 b /\ gmo w1 w2.

  (* The deleted duplicate d and its keeper k. *)
  Variables d k : Event.
  Hypothesis d_in : In d E0.
  Hypothesis k_in : In k E0.
  Hypothesis d_w  : is_write d.

  (* Adjacency at byte b (gamma_adj, edge form): d and k both touch b, and no b-touching write in E0
     lies strictly gmo-between them in either direction. *)
  Definition adj (b : Byte) : Prop :=
    touches d b /\ touches k b /\
    forall w, In w E0 -> is_write w -> touches w b ->
      ~ (gmo d w /\ gmo w k) /\ ~ (gmo k w /\ gmo w d).

  (* ---- co-edge lift: witness co among survivors IS a fault co edge (inclusion). ---- *)
  Lemma co_survivor_is_fault :
    forall b w1 w2, w1 <> d -> w2 <> d -> coF b w1 w2 -> coF b w1 w2.
  Proof. intros b w1 w2 _ _ H; exact H. Qed.

  (* ---- fr-edge lift crux: the fault-run supporting order gmo d w2 follows from the witness order
     gmo k w2 BECAUSE d and k are adjacent. ---- *)
  Lemma fr_lift_core :
    gmo_wf ->
    forall b w2,
      adj b ->
      In w2 E0 -> is_write w2 -> touches w2 b -> w2 <> d ->
      gmo k w2 ->          (* witness coherence: keeper before w2 *)
      gmo d w2.            (* fault-run coherence: deleted duplicate before w2 *)
  Proof.
    intros Hwf b w2 Hadj Hw2in Hw2w Hw2t Hne Gkw2.
    destruct Hadj as [_ [_ Hbet]].
    destruct Hwf as [_ _ Gtot].
    destruct (Gtot d w2 d_in Hw2in (fun E => Hne (eq_sym E))) as [Gdw2 | Gw2d].
    - exact Gdw2.
    - exfalso.
      destruct (Hbet w2 Hw2in Hw2w Hw2t) as [_ Hkd].
      apply Hkd. split; [exact Gkw2 | exact Gw2d].
  Qed.

  (* Packaged fr lift: the full fault-run fr-supporting co edge d <co w2 exists. *)
  Theorem fr_edge_lifts :
    gmo_wf ->
    forall b w2,
      adj b ->
      In w2 E0 -> is_write w2 -> touches w2 b -> w2 <> d ->
      gmo k w2 ->
      coF b d w2.
  Proof.
    intros Hwf b w2 Hadj Hw2in Hw2w Hw2t Hne Gkw2.
    assert (Tdb : touches d b) by (destruct Hadj as [T _]; exact T).
    split; [exact d_in|]. split; [exact Hw2in|]. split; [exact d_w|].
    split; [exact Hw2w|]. split; [exact Tdb|]. split; [exact Hw2t|].
    apply (fr_lift_core Hwf b w2 Hadj Hw2in Hw2w Hw2t Hne Gkw2).
  Qed.

End EdgeLift.
