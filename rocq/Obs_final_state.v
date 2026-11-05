(* Obs_final_state.v — RESTART-V M4: co-max (final-memory-value) preservation.

   Observation of an execution = (values reads return) + (final memory state). L1 already proves the
   first half (`L1_erasure_preserves_read_values`). This file proves the coherence-latest write's
   value is preserved by erasure — the value half of the final memory state:

     given the fault run's gmo-maximal write to byte b (w_f), there EXISTS a witness (survivor)
     gmo-maximal write to b with the SAME value.  (`final_state_preserved_exists`)

   Why (round-14 audit made this the primary, existential form): if the fault co-max w_f is not the
   deleted duplicate d, it survives and stays co-max; if w_f = d, the whole-footprint-equal keeper k
   (a survivor) is the new survivor co-max — every survivor b-write is gmo-before d (d was co-max)
   and, by gamma_adj, not strictly between k and d, so it is k or gmo-before k; and k has d's value.
   Either way a survivor co-max exists with the same value.

   HONESTY SCOPE (round-14 audit). This is co-max-VALUE preservation, NOT by itself full final-memory
   preservation: it says nothing about a byte that NO write touches (where real memory keeps its
   initial value). Full final-memory preservation additionally needs, per byte, either a write to
   exist or an explicit initial-value fallback — a modelling choice for the concrete-execution layer.
   Stated over abstract gmo / co-max, not a concrete memory-array semantics. Self-contained; 0
   Admitted / 0 axioms (Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Import ListNotations.

Section FinalState.

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte : Type.
  Variable Value : Type.
  Variable gmo : Event -> Event -> Prop.
  Variable is_write : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable wval : Event -> Byte -> Value.
  Variable E0 : list Event.

  Record gmo_wf : Prop := {
    g_irr : forall e, In e E0 -> ~ gmo e e;
    g_tr  : forall a b c, In a E0 -> In b E0 -> In c E0 -> gmo a b -> gmo b c -> gmo a c;
    g_tot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a
  }.

  Variables d k : Event.

  Definition survivor (x : Event) : Prop := In x E0 /\ x <> d.
  Definition inE0 (x : Event) : Prop := In x E0.

  Definition co_max_of (C : Event -> Prop) (b : Byte) (w : Event) : Prop :=
    is_write w /\ touches w b /\ C w /\
    (forall w', C w' -> is_write w' -> touches w' b -> w' = w \/ gmo w' w).

  Lemma comax_unique :
    gmo_wf ->
    forall (C : Event -> Prop) b w1 w2,
      (forall x, C x -> In x E0) ->
      co_max_of C b w1 -> co_max_of C b w2 -> w1 = w2.
  Proof.
    intros [Girr Gtr Gtot] C b w1 w2 Hsub H1 H2.
    destruct H1 as [W1 [T1 [C1 M1]]]. destruct H2 as [W2 [T2 [C2 M2]]].
    destruct (M1 w2 C2 W2 T2) as [E|G21].
    - symmetry; exact E.
    - destruct (M2 w1 C1 W1 T1) as [E2|G12].
      + exact E2.
      + exfalso. apply (Girr w1 (Hsub w1 C1)).
        apply (Gtr w1 w2 w1 (Hsub w1 C1) (Hsub w2 C2) (Hsub w1 C1) G12 G21).
  Qed.

  (* Duplicate-pair interface (only the facts the proof actually uses — round-14 audit removed the
     unused keeper_before / d_in / d_w: d's membership and write-ness come from its co-maximality). *)
  Hypothesis k_in : In k E0.
  Hypothesis k_w  : is_write k.
  Hypothesis kd_ne : k <> d.
  Hypothesis foot_dk : forall b, touches d b -> touches k b.        (* k covers d's footprint *)
  Hypothesis dup_val : forall b, touches d b -> wval k b = wval d b. (* equal duplicate values *)
  Hypothesis adj_kd :                                                 (* gamma_adj, k..d direction *)
    forall b, touches d b ->
      forall w, In w E0 -> is_write w -> touches w b -> ~ (gmo k w /\ gmo w d).

  Lemma Hsub_sv : forall x, survivor x -> In x E0.
  Proof. intros x [Hx _]; exact Hx. Qed.

  (* Primary (existential) form: a fault co-max at b yields a survivor co-max at b of equal value. *)
  Theorem final_state_preserved_exists :
    gmo_wf ->
    forall b w_f,
      co_max_of inE0 b w_f ->
      exists w_n, co_max_of survivor b w_n /\ wval w_f b = wval w_n b.
  Proof.
    intros Hwf b w_f Hf.
    assert (Gtot := g_tot Hwf).
    destruct Hf as [Wf [Tf [Inf Hmaxf]]].
    destruct (eq_ev_dec w_f d) as [Efd | Nfd].
    - (* w_f = d : keeper k is the survivor co-max *)
      subst w_f.
      exists k. split.
      + split; [exact k_w|]. split; [apply foot_dk; exact Tf|].
        split; [split; [exact k_in | exact kd_ne]|].
        intros w' [Inw' Nw'd] Ww' Tw'.
        destruct (eq_ev_dec w' k) as [Ek|Nk]; [left; exact Ek | right].
        destruct (Hmaxf w' Inw' Ww' Tw') as [Ewd|Gwd].
        * exfalso; apply Nw'd; exact Ewd.
        * destruct (Gtot w' k Inw' k_in Nk) as [Gw'k|Gkw'].
          -- exact Gw'k.
          -- exfalso. apply (adj_kd b Tf w' Inw' Ww' Tw'). split; [exact Gkw' | exact Gwd].
      + symmetry. apply dup_val. exact Tf.
    - (* w_f <> d : w_f survives and stays co-max over survivors *)
      exists w_f. split.
      + split; [exact Wf|]. split; [exact Tf|].
        split; [split; [exact Inf | exact Nfd]|].
        intros w' [Inw' _] Ww' Tw'. apply (Hmaxf w' Inw' Ww' Tw').
      + reflexivity.
  Qed.

  (* Corollary: any two co-max writes (fault and witness) have equal value — via uniqueness. *)
  Corollary final_state_preserved :
    gmo_wf ->
    forall b w_f w_n,
      co_max_of inE0 b w_f -> co_max_of survivor b w_n ->
      wval w_f b = wval w_n b.
  Proof.
    intros Hwf b w_f w_n Hf Hn.
    destruct (final_state_preserved_exists Hwf b w_f Hf) as [w_n0 [Hn0 Hval0]].
    assert (Ewn : w_n = w_n0)
      by (apply (comax_unique Hwf survivor b w_n w_n0 Hsub_sv Hn Hn0)).
    subst w_n. exact Hval0.
  Qed.

End FinalState.
