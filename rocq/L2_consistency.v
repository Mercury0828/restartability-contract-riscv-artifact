(* L2_consistency.v — RESTART-V M4, Layer 2 (partial): C1 derived inclusions co/rfe/fr ⊆ gmo.

   Mechanizes D-a v1.2 §C1: "Given C4, co ∪ rfe ∪ fr ⊆ gmo is derived." These three inclusions are
   what makes the main-model acyclicity check C2 (acyclic(co ∪ rfe ∪ fr ∪ ppo)) reduce to
   ppo ⊆ gmo — every non-PPO edge is already gmo-forward. `fr ⊆ gmo` is the one with real content:
   it uses the C4 load-value maximality (a coherence-later store cannot be an earlier candidate than
   the read's source).

   Self-contained; 0 Admitted / 0 axioms (Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Import ListNotations.

Section L2_consistency.

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte  : Type.
  Variable is_write : Event -> Prop.
  Variable is_read  : Event -> Prop.
  Variable touches  : Event -> Byte -> Prop.

  Variable E0  : list Event.
  Variable gmo : Event -> Event -> Prop.

  Record gmo_wf : Prop := {
    gmo_irrefl : forall e, In e E0 -> ~ gmo e e;
    gmo_trans  : forall a b c, In a E0 -> In b E0 -> In c E0 ->
                               gmo a b -> gmo b c -> gmo a c;
    gmo_total  : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a
  }.

  Variable rf : Event -> Byte -> Event -> Prop.
  Variable po : Event -> Event -> Prop.

  Variable Hart : Type.
  Variable hart : Event -> Hart.

  Definition cand (b : Byte) (r w : Event) : Prop :=
    In w E0 /\ is_write w /\ touches w b /\ (gmo w r \/ po w r).

  Definition C4_source (b : Byte) (r w : Event) : Prop :=
    cand b r w /\ forall w', cand b r w' -> w' = w \/ gmo w' w.

  Definition co (b : Byte) (w1 w2 : Event) : Prop :=
    is_write w1 /\ is_write w2 /\ touches w1 b /\ touches w2 b /\
    gmo w1 w2 /\ In w1 E0 /\ In w2 E0.

  Definition fr (b : Byte) (r w2 : Event) : Prop :=
    exists w1, rf w1 b r /\ co b w1 w2.

  (* Interface: rf realizes the C4 load-value rule; po is intra-hart; reads and writes disjoint. *)
  Hypothesis rf_is_C4 :
    forall b r w, rf w b r -> is_read r -> In r E0 -> C4_source b r w.
  Hypothesis po_same_hart :
    forall a c, po a c -> hart a = hart c.
  Hypothesis rw_disjoint :
    forall e, is_read e -> is_write e -> False.

  (* co ⊆ gmo (definitional). *)
  Lemma co_sub_gmo : forall b w1 w2, co b w1 w2 -> gmo w1 w2.
  Proof. intros b w1 w2 [_ [_ [_ [_ [H _]]]]]; exact H. Qed.

  (* rfe ⊆ gmo: an external (cross-hart) rf source is gmo-before the read (it cannot be po-before). *)
  Lemma rfe_sub_gmo :
    forall b r w,
      is_read r -> In r E0 ->
      rf w b r -> hart w <> hart r ->
      gmo w r.
  Proof.
    intros b r w Hrd Hr0 Hrf Hext.
    destruct (rf_is_C4 b r w Hrf Hrd Hr0) as [[Inw [Ww [Tw Hord]]] _].
    destruct Hord as [Gwr|Pwr].
    - exact Gwr.
    - exfalso. apply Hext. apply po_same_hart. exact Pwr.
  Qed.

  (* fr ⊆ gmo: if r reads w1 and w1 <_co w2, then gmo r w2 (else w2 would beat the C4 source). *)
  Lemma fr_sub_gmo :
    gmo_wf ->
    forall b r w2,
      is_read r -> In r E0 ->
      fr b r w2 ->
      gmo r w2.
  Proof.
    intros [Hirr Htr Htot] b r w2 Hrd Hr0 [w1 [Hrf Hco]].
    destruct Hco as [Ww1 [Ww2 [Tw1 [Tw2 [Gw1w2 [Inw1 Inw2]]]]]].
    destruct (rf_is_C4 b r w1 Hrf Hrd Hr0) as [Hcand1 Hmax1].
    assert (Hne : r <> w2). { intro E. subst w2. apply (rw_disjoint r Hrd Ww2). }
    destruct (Htot r w2 Hr0 Inw2 Hne) as [Grw2|Gw2r].
    - exact Grw2.
    - exfalso.
      assert (Hcw2 : cand b r w2).
      { split; [exact Inw2|]. split; [exact Ww2|]. split; [exact Tw2|]. left; exact Gw2r. }
      destruct (Hmax1 w2 Hcw2) as [E2|G2].
      + subst w2. apply (Hirr w1 Inw1). exact Gw1w2.
      + apply (Hirr w1 Inw1). apply (Htr w1 w2 w1 Inw1 Inw2 Inw1 Gw1w2 G2).
  Qed.

  (* Corollary: a relation contained in gmo is irreflexive on the carrier (per-edge acyclicity).
     Full-path acyclicity of co ∪ rfe ∪ fr ∪ ppo (= C2) then follows once ppo ⊆ gmo is instantiated
     and transitive closure is threaded — the remaining L2 obligation. *)
  Lemma sub_gmo_irrefl :
    gmo_wf ->
    forall (R : Event -> Event -> Prop),
      (forall x y, In x E0 -> In y E0 -> R x y -> gmo x y) ->
      forall x, In x E0 -> ~ R x x.
  Proof.
    intros [Hirr _ _] R Hsub x Hx HRxx.
    apply (Hirr x Hx). apply (Hsub x x Hx Hx HRxx).
  Qed.

  (* Full-path C2: the transitive closure of any carrier-relation contained in gmo stays in gmo,
     hence is irreflexive — the main-model acyclicity check. Instantiate U = co ∪ rfe ∪ fr ∪ ppo. *)
  Lemma ct_in_gmo :
    gmo_wf ->
    forall (U : Event -> Event -> Prop),
      (forall x y, U x y -> In x E0 /\ In y E0 /\ gmo x y) ->
      forall x y, clos_trans Event U x y -> In x E0 /\ In y E0 /\ gmo x y.
  Proof.
    intros Hwf U HU x y H.
    induction H as [x y HU0 | x m z H1 IH1 H2 IH2].
    - apply HU; exact HU0.
    - destruct IH1 as [Ix [Im Gxm]]. destruct IH2 as [Im' [Iz Gmz]].
      destruct Hwf as [_ Htr _].
      split; [exact Ix|]. split; [exact Iz|]. apply (Htr x m z Ix Im Iz Gxm Gmz).
  Qed.

  Theorem C2_acyclic :
    gmo_wf ->
    forall (U : Event -> Event -> Prop),
      (forall x y, U x y -> In x E0 /\ In y E0 /\ gmo x y) ->
      forall x, ~ clos_trans Event U x x.
  Proof.
    intros Hwf U HU x Hcyc.
    destruct (ct_in_gmo Hwf U HU x x Hcyc) as [Ix [_ Gxx]].
    destruct Hwf as [Hirr _ _]. apply (Hirr x Ix). exact Gxx.
  Qed.

  (* ---- Concrete C2: assemble the actual main-model union and reduce its acyclicity to ppo ⊆ gmo.

     This closes round-11 audit finding F3: `C2_acyclic` above is the generic "sub-relation of a
     strict order is acyclic". Here we build the CONCRETE RVWMO main-model relation
     co ∪ rfe ∪ fr ∪ ppo and prove it ⊆ gmo using the three derived inclusions (co/rfe/fr) plus a
     single named hypothesis `ppo_sub_gmo`. Instantiating C2_acyclic then gives the concrete
     main-model acyclicity check, honestly reduced to exactly one remaining obligation: ppo ⊆ gmo
     (the standard endpoint of every axiomatic RVWMO consistency proof; discharging it means
     mechanizing PPO rules r1-r13, the remaining concrete L2 work). *)

  Variable ppo : Event -> Event -> Prop.
  (* NB (round-12 audit): this hypothesis bundles PPO endpoint carrier-closure (In x/y E0) WITH the
     order fact ppo ⊆ gmo. So the honest reduction is "to PPO carrier-closure + ppo ⊆ gmo". In a
     concrete execution where ppo is defined only over E0, the carrier-closure part is immediate. *)
  Hypothesis ppo_sub_gmo : forall x y, ppo x y -> In x E0 /\ In y E0 /\ gmo x y.

  Inductive main_edge : Event -> Event -> Prop :=
  | me_co  : forall b w1 w2, co b w1 w2 -> main_edge w1 w2
  | me_rfe : forall b r w, is_read r -> In r E0 -> rf w b r -> hart w <> hart r -> main_edge w r
  | me_fr  : forall b r w, is_read r -> In r E0 -> fr b r w -> main_edge r w
  | me_ppo : forall x y, ppo x y -> main_edge x y.

  Lemma main_edge_sub_gmo :
    gmo_wf ->
    forall x y, main_edge x y -> In x E0 /\ In y E0 /\ gmo x y.
  Proof.
    intros Hwf x y H. destruct H as [b w1 w2 Hco | b r w Hrd Hr0 Hrf Hext | b r w Hrd Hr0 Hfr | x y Hppo].
    - (* co *) destruct Hco as [_ [_ [_ [_ [Gw [Inw1 Inw2]]]]]].
      split; [exact Inw1|]. split; [exact Inw2|]. exact Gw.
    - (* rfe *) destruct (rf_is_C4 b r w Hrf Hrd Hr0) as [[Inw _] _].
      split; [exact Inw|]. split; [exact Hr0|].
      apply (rfe_sub_gmo b r w Hrd Hr0 Hrf Hext).
    - (* fr *) assert (Inw : In w E0).
      { destruct Hfr as [w1 [_ Hco]]. destruct Hco as [_ [_ [_ [_ [_ [_ I]]]]]]. exact I. }
      split; [exact Hr0|]. split; [exact Inw|].
      apply (fr_sub_gmo Hwf b r w Hrd Hr0). exact Hfr.
    - (* ppo *) apply ppo_sub_gmo; exact Hppo.
  Qed.

  (* Concrete main-model acyclicity check acyclic(co ∪ rfe ∪ fr ∪ ppo), reduced to ppo ⊆ gmo. *)
  Theorem Main_model_acyclic :
    gmo_wf -> forall x, ~ clos_trans Event main_edge x x.
  Proof.
    intros Hwf. apply (C2_acyclic Hwf main_edge (main_edge_sub_gmo Hwf)).
  Qed.

End L2_consistency.
