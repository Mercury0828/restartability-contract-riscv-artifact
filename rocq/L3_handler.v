(* L3_handler.v — RESTART-V M4, Layer 3 (structural): handler state discipline L1 / L1b.

   Mechanizes the STRUCTURE of the two handler lemmas (D-a v1.2 §6.4/§6.5) at the state-machine
   level, abstracting away the 71-instruction encoding and PMP bitvector arithmetic:

     L1  (U-state restoration): the handler is `save xT into mscratch; body; restore xT`, where the
         body writes only xT. Then every register other than xT/mscratch is unchanged, and xT is
         restored to its initial value.
     L1b (PMP repair):          writing the designated entry d sets d and leaves every other entry
         untouched.

   The concrete instruction-level refinement (the exact H00..H14 image realises this save/body/
   restore shape, and the fixed pmpcfg/pmpaddr constants realise pmp_ok) is the remaining L3 work.
   Self-contained; 0 Admitted / 0 axioms (Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Import ListNotations.

Section Handler.

  Variable Reg : Type.
  Variable eq_reg : forall x y : Reg, {x = y} + {x <> y}.
  Variable Value : Type.

  Definition State := Reg -> Value.
  Definition upd (s : State) (r : Reg) (v : Value) : State :=
    fun r' => if eq_reg r' r then v else s r'.

  Lemma upd_same : forall s r v, upd s r v r = v.
  Proof. intros s r v. unfold upd. destruct (eq_reg r r) as [_|N]; [reflexivity | exfalso; apply N; reflexivity]. Qed.

  Lemma upd_other : forall s r v r', r' <> r -> upd s r v r' = s r'.
  Proof. intros s r v r' H. unfold upd. destruct (eq_reg r' r) as [E|N]; [exfalso; apply H; exact E | reflexivity]. Qed.

  Variables xT mscratch : Reg.
  Hypothesis xT_ms_distinct : xT <> mscratch.

  (* body writes only xT (never mscratch, never any other U register). *)
  Variable body : State -> State.
  Hypothesis body_only_xT : forall s r, r <> xT -> body s r = s r.

  Definition handler (s : State) : State :=
    let s1 := upd s mscratch (s xT) in     (* save:    mscratch := xT *)
    let s2 := body s1 in                    (* body:    writes only xT *)
    upd s2 xT (s2 mscratch).                (* restore: xT := mscratch *)

  (* L1 (part 1): every register other than xT and mscratch is preserved. *)
  Theorem handler_preserves_others :
    forall s r, r <> xT -> r <> mscratch -> handler s r = s r.
  Proof.
    intros s r Hx Hm. unfold handler.
    rewrite (upd_other _ xT _ r Hx).
    rewrite (body_only_xT _ r Hx).
    rewrite (upd_other _ mscratch _ r Hm).
    reflexivity.
  Qed.

  (* L1 (part 2): xT is restored to its initial value. *)
  Theorem handler_restores_xT :
    forall s, handler s xT = s xT.
  Proof.
    intro s. unfold handler.
    rewrite (upd_same (body (upd s mscratch (s xT))) xT).
    assert (Hms : mscratch <> xT) by (apply not_eq_sym; exact xT_ms_distinct).
    rewrite (body_only_xT (upd s mscratch (s xT)) mscratch Hms).
    rewrite (upd_same s mscratch (s xT)).
    reflexivity.
  Qed.

  (* Corollary: the whole U-GPR state (every register except mscratch) is preserved by the handler.
     This is exactly L1's "handler restores U GPRs". *)
  Theorem handler_preserves_U :
    forall s r, r <> mscratch -> handler s r = s r.
  Proof.
    intros s r Hm. destruct (eq_reg r xT) as [Ex|Nx].
    - subst r. apply handler_restores_xT.
    - apply handler_preserves_others; [exact Nx | exact Hm].
  Qed.

End Handler.

Section PMP.

  Variable Idx : Type.
  Variable eq_idx : forall x y : Idx, {x = y} + {x <> y}.
  Variable Entry : Type.

  Definition PMP := Idx -> Entry.
  Definition pupd (t : PMP) (d : Idx) (e : Entry) : PMP :=
    fun i => if eq_idx i d then e else t i.

  (* L1b (part 1): the designated entry receives its new (pmp_ok) value. *)
  Theorem pmp_update_designated : forall t d e, pupd t d e d = e.
  Proof. intros t d e. unfold pupd. destruct (eq_idx d d) as [_|N]; [reflexivity | exfalso; apply N; reflexivity]. Qed.

  (* L1b (part 2): every other entry is untouched. *)
  Theorem pmp_update_local : forall t d e q, q <> d -> pupd t d e q = t q.
  Proof. intros t d e q H. unfold pupd. destruct (eq_idx q d) as [E|N]; [exfalso; apply H; exact E | reflexivity]. Qed.

End PMP.
