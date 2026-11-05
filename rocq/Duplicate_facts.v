(* Duplicate_facts.v — RESTART-V M4: foot_dk (D3) and dup_val (B13) are DERIVABLE from DupPair (B9).

   The assumption report lists `foot_dk` (keeper covers the deleted duplicate's footprint) and
   `dup_val` (equal duplicate values) as hypotheses of the closed T1 export. This file shows they are
   NOT independent: both follow from `DupPair p q` (whole-footprint-equal duplicate pair) together
   with `d,k ∈ {p,q}`, `k` the keeper. So the honest assumption count for those is 0 beyond DupPair.
   Self-contained modulo L1; 0 Admitted / 0 axioms. Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import RestartV.L1_abstract_erasure.
Import ListNotations.

Section DuplicateFacts.

  Variable Event : Type.
  Variable Byte : Type.
  Variable Value : Type.
  Variable is_write : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable wval : Event -> Byte -> Value.
  Variables p q k d : Event.

  Hypothesis Hdup : DupPair Event Byte Value is_write touches wval p q.
  (* {d,k} = {p,q}, k the keeper, d the deleted: the two admissible labelings *)
  Hypothesis Hlabel : (d = p /\ k = q) \/ (d = q /\ k = p).

  (* D3: keeper covers the deleted duplicate's footprint (from dp_foot). *)
  Theorem foot_dk_from_DupPair : forall b, touches d b -> touches k b.
  Proof.
    intros b Hdb. destruct Hdup as [_ _ Dfoot _]. destruct Hlabel as [[Ed Ek]|[Ed Ek]]; subst d k.
    - apply (proj1 (Dfoot b)); exact Hdb.
    - apply (proj2 (Dfoot b)); exact Hdb.
  Qed.

  (* B13: equal duplicate values (from dp_val, using dp_foot for the q-labeled case). *)
  Theorem dup_val_from_DupPair : forall b, touches d b -> wval k b = wval d b.
  Proof.
    intros b Hdb. destruct Hdup as [_ _ Dfoot Dval]. destruct Hlabel as [[Ed Ek]|[Ed Ek]]; subst d k.
    - (* d=p, k=q: wval q b = wval p b, i.e. symmetry of dp_val at p (touches p b = Hdb) *)
      symmetry. apply Dval; exact Hdb.
    - (* d=q, k=p: wval p b = wval q b = dp_val at p; touches p b from dp_foot backward *)
      apply Dval. apply (proj2 (Dfoot b)); exact Hdb.
  Qed.

End DuplicateFacts.
