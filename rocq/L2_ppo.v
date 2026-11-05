(* L2_ppo.v — RESTART-V M4, Layer 2 (partial): per-location coherence C3-B via a measure.

   Mechanizes D-a v1.2 §C3 (the "source-write-rank" argument, with the R->W strictness the delta
   audit asked to make explicit). The per-byte coherence relation co ∪ rf ∪ fr ∪ po-loc is acyclic
   because it is non-decreasing in the measure
       m(write w) = 2 * rank(w),   m(read r) = 2 * rank(src r) + 1,
   with the ONLY equal-measure edges being same-source read->read po-loc steps, which are program
   order and therefore acyclic.

   Two reusable order-theory principles are proved first (acyclic_strict_measure,
   acyclic_weak_measure), then C3-B is their instantiation. Self-contained; 0 Admitted / 0 axioms
   (Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Relations.Relations.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* ---------------- Reusable acyclicity principles ---------------- *)

Section Measures.
  Variable A : Type.

  (* A relation strictly decreasing a nat-measure is acyclic. *)
  Lemma acyclic_strict_measure :
    forall (U : A -> A -> Prop) (m : A -> nat),
      (forall x y, U x y -> m x < m y) ->
      forall x, ~ clos_trans A U x x.
  Proof.
    intros U m Hstrict x Hcyc.
    assert (G : forall a b, clos_trans A U a b -> m a < m b).
    { intros a b H. induction H as [a b HU | a c b H1 IH1 H2 IH2].
      - apply Hstrict; exact HU.
      - exact (Nat.lt_trans _ _ _ IH1 IH2). }
    exact (Nat.lt_irrefl (m x) (G x x Hcyc)).
  Qed.

  (* A relation non-decreasing in a nat-measure, whose equal-measure sub-relation is acyclic,
     is itself acyclic. *)
  Lemma acyclic_weak_measure :
    forall (U : A -> A -> Prop) (m : A -> nat),
      (forall x y, U x y -> m x <= m y) ->
      (forall x, ~ clos_trans A (fun a b => U a b /\ m a = m b) x x) ->
      forall x, ~ clos_trans A U x x.
  Proof.
    intros U m Hmono Heq x Hcyc.
    (* around a cycle the measure is constant, so every edge is an equal-measure edge *)
    assert (Hle : forall a b, clos_trans A U a b -> m a <= m b).
    { intros a b H. induction H as [a b HU | a c b H1 IH1 H2 IH2].
      - apply Hmono; exact HU.
      - exact (Nat.le_trans _ _ _ IH1 IH2). }
    assert (Hlift : forall a b, clos_trans A U a b -> m a = m b ->
                    clos_trans A (fun a b => U a b /\ m a = m b) a b).
    { intros a b H. induction H as [a b HU | a c b H1 IH1 H2 IH2]; intro Heqab.
      - apply t_step. split; [exact HU | exact Heqab].
      - assert (Hac : m a <= m c) by (apply Hle; exact H1).
        assert (Hcb : m c <= m b) by (apply Hle; exact H2).
        assert (Emac : m a = m c) by (apply Nat.le_antisymm; [exact Hac | rewrite Heqab; exact Hcb]).
        assert (Emcb : m c = m b) by (rewrite <- Emac; exact Heqab).
        apply (t_trans A _ a c b).
        + apply IH1; exact Emac.
        + apply IH2; exact Emcb. }
    apply (Heq x). apply Hlift; [exact Hcyc | reflexivity].
  Qed.

End Measures.

(* ---------------- C3-B: per-byte coherence acyclicity ---------------- *)

Section C3B.

  Variable Event : Type.
  Variable isw : Event -> bool.            (* true = write, false = read (they partition) *)
  Variable rank : Event -> nat.            (* gmo-rank realizing coherence among writes *)
  Variable src  : Event -> Event.          (* rf source of a read *)

  (* The four per-byte relations (already restricted to the fixed byte b). *)
  Variable co rf fr poloc : Event -> Event -> Prop.

  Definition m (e : Event) : nat :=
    if isw e then 2 * rank e else 2 * rank (src e) + 1.

  Definition Ubyte (x y : Event) : Prop := co x y \/ rf x y \/ fr x y \/ poloc x y.

  (* Classification hypotheses = D-a §C3 facts derived from C4 + r1 + r2 (taken here as the
     per-byte interface these rules provide). *)
  Hypothesis H_co :
    forall w1 w2, co w1 w2 -> isw w1 = true /\ isw w2 = true /\ rank w1 < rank w2.
  Hypothesis H_rf :
    forall w r, rf w r -> isw w = true /\ isw r = false /\ w = src r.
  Hypothesis H_fr :
    forall r w, fr r w -> isw r = false /\ isw w = true /\ rank (src r) < rank w.
  Hypothesis H_poloc :
    forall x y, poloc x y ->
      (isw x = true  /\ isw y = true  /\ rank x < rank y) \/
      (isw x = false /\ isw y = true  /\ rank (src x) < rank y) \/
      (isw x = true  /\ isw y = false /\ rank x <= rank (src y)) \/
      (isw x = false /\ isw y = false /\ rank (src x) <= rank (src y)).

  (* po-loc is a strict partial order (used only to kill equal-measure read->read cycles). *)
  Hypothesis poloc_irrefl : forall x, ~ poloc x x.
  Hypothesis poloc_trans  : forall x y z, poloc x y -> poloc y z -> poloc x z.

  Lemma m_mono : forall x y, Ubyte x y -> m x <= m y.
  Proof.
    intros x y HU. destruct HU as [Hco|[Hrf|[Hfr|Hpl]]]; unfold m.
    - destruct (H_co x y Hco) as [Ex [Ey Hr]]. rewrite Ex, Ey; cbn; lia.
    - destruct (H_rf x y Hrf) as [Ex [Ey Hs]]. rewrite Ex, Ey; cbn; rewrite Hs; lia.
    - destruct (H_fr x y Hfr) as [Ex [Ey Hr]]. rewrite Ex, Ey; cbn; lia.
    - destruct (H_poloc x y Hpl) as [[Ex [Ey Hr]]|[[Ex [Ey Hr]]|[[Ex [Ey Hr]]|[Ex [Ey Hr]]]]];
        rewrite Ex, Ey; cbn; lia.
  Qed.

  (* The only equal-measure Ubyte edges are po-loc edges (all others strictly increase m). *)
  Lemma eqm_is_poloc : forall x y, Ubyte x y -> m x = m y -> poloc x y.
  Proof.
    intros x y HU Heq. destruct HU as [Hco|[Hrf|[Hfr|Hpl]]].
    - exfalso. destruct (H_co x y Hco) as [Ex [Ey Hr]].
      unfold m in Heq; rewrite Ex, Ey in Heq; cbn in Heq; lia.
    - exfalso. destruct (H_rf x y Hrf) as [Ex [Ey Hs]].
      unfold m in Heq; rewrite Ex, Ey, Hs in Heq; cbn in Heq; lia.
    - exfalso. destruct (H_fr x y Hfr) as [Ex [Ey Hr]].
      unfold m in Heq; rewrite Ex, Ey in Heq; cbn in Heq; lia.
    - exact Hpl.
  Qed.

  Theorem C3B_acyclic : forall x, ~ clos_trans Event Ubyte x x.
  Proof.
    apply (acyclic_weak_measure Event Ubyte m).
    - exact m_mono.
    - (* equal-measure sub-relation is acyclic: it is contained in po-loc, a strict order *)
      intro x.
      assert (Hsub : forall a b, clos_trans Event (fun a b => Ubyte a b /\ m a = m b) a b -> poloc a b).
      { intros a b H. induction H as [a b [HU Heq] | a c b H1 IH1 H2 IH2].
        - apply eqm_is_poloc; [exact HU | exact Heq].
        - apply (poloc_trans a c b IH1 IH2). }
      intro Hcyc. apply (poloc_irrefl x). apply Hsub; exact Hcyc.
  Qed.

End C3B.

(* ---------------- C3-G preservation: edge-path simulation ---------------- *)
(* The delta-audit DELTA 3 backbone: D-a v1.1/v1.2 preserve the GLOBAL per-location Cat check
   acyclic(co ∪ rf ∪ fr ∪ po-loc) on the constructed no-fault witness NOT by inferring it from
   per-byte C3-B, but by direct edge-path simulation — every witness edge expands to a nonempty
   path in the fault-run relation with the same retained endpoints. This principle (a relation whose
   every edge lifts to a path in an acyclic relation is itself acyclic) is that argument's core. *)

Section Simulation.
  Variable A : Type.

  Lemma clos_trans_lift :
    forall (U V : A -> A -> Prop),
      (forall x y, V x y -> clos_trans A U x y) ->
      forall x y, clos_trans A V x y -> clos_trans A U x y.
  Proof.
    intros U V Hlift x y H. induction H as [x y HV | x z y H1 IH1 H2 IH2].
    - apply Hlift; exact HV.
    - apply (t_trans A U x z y IH1 IH2).
  Qed.

  (* If every V-edge lifts to a U-path and U is acyclic, then V is acyclic.
     Instantiate: V = witness (no-fault) po-loc coherence, U = fault-run po-loc coherence. *)
  Theorem acyclic_via_simulation :
    forall (U V : A -> A -> Prop),
      (forall x y, V x y -> clos_trans A U x y) ->
      (forall x, ~ clos_trans A U x x) ->
      forall x, ~ clos_trans A V x x.
  Proof.
    intros U V Hlift Hacyc x Hcyc.
    apply (Hacyc x). apply (clos_trans_lift U V Hlift x x Hcyc).
  Qed.

End Simulation.
