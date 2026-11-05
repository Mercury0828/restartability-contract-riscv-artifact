(* R2_counterexample.v — RESTART-V M4: the alleged r2 counterexample is per-location INCONSISTENT.

   web-Pro #3 regression (suggested test 3): during the r2 analysis a scenario was proposed — an
   observer's two same-byte loads a,b (a po-before b) with `a` reading the deleted duplicate `d` and
   `b` reading the keeper `k`, where `gmo k d` (k coherence-earlier). It looked like it might break
   T1. web-Pro showed it does NOT exist: that fault execution is itself INCONSISTENT, because it
   contains the per-location cycle

       d --rf--> a --po-loc--> b --fr--> d

   (the fr edge b→d holds because b reads k and k <co d). This file mechanizes exactly that: from the
   four pattern facts, the per-location relation has a cycle at d, so the C3 check rejects it. Hence
   no such consistent X_F exists, and the contraction never faces it. Self-contained; 0 Admitted /
   0 axioms. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Import ListNotations.

Section R2Counterexample.

  Variable Event : Type.
  Variable Byte : Type.
  Variable gmo : Event -> Event -> Prop.
  Variable is_write : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable rf : Event -> Byte -> Event -> Prop.   (* rf w x r : r reads w at byte x *)
  Variable poloc : Event -> Event -> Prop.         (* same-byte program order between accesses *)

  (* per-location edges: rf (write->read), po-loc, and fr (read->coherence-later write). *)
  Definition fr (bx : Byte) (r w2 : Event) : Prop :=
    exists w1, rf w1 bx r /\ is_write w2 /\ touches w2 bx /\ gmo w1 w2.

  Definition R (x y : Event) : Prop :=
    (exists bx, rf x bx y) \/ poloc x y \/ (exists bx, fr bx x y).

  (* the alleged counterexample pattern *)
  Variables k d a b : Event.
  Variable bx : Byte.
  Hypothesis co_kd  : gmo k d.          (* k coherence-earlier than d (same byte) *)
  Hypothesis d_w    : is_write d.
  Hypothesis d_tch  : touches d bx.
  Hypothesis rf_da  : rf d bx a.        (* a reads the deleted duplicate d *)
  Hypothesis rf_kb  : rf k bx b.        (* b reads the keeper k *)
  Hypothesis poloc_ab : poloc a b.      (* a is po-before b at byte bx *)

  (* The pattern forms a per-location cycle d -> a -> b -> d, so the execution is C3-inconsistent. *)
  Theorem alleged_counterexample_is_cyclic : clos_trans Event R d d.
  Proof.
    apply (t_trans Event R d b d).
    - apply (t_trans Event R d a b).
      + apply t_step. left. exists bx. exact rf_da.                 (* d --rf--> a *)
      + apply t_step. right. left. exact poloc_ab.                  (* a --po-loc--> b *)
    - apply t_step. right. right. exists bx.                        (* b --fr--> d *)
      exists k. split; [exact rf_kb|]. split; [exact d_w|]. split; [exact d_tch | exact co_kd].
  Qed.

  (* Consequently any per-location acyclicity check (C3) rejects the pattern: no consistent fault
     execution realises "a reads d, b reads k, gmo k d, a po-loc-before b". *)
  Corollary alleged_counterexample_not_C3_acyclic :
    ~ (forall x, ~ clos_trans Event R x x).
  Proof. intro Hacyc. exact (Hacyc d alleged_counterexample_is_cyclic). Qed.

End R2Counterexample.
