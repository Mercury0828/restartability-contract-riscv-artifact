(* T1_frozen_instantiated.v — RESTART-V M4: WIRE the token-model RO-adapter INTO the capstone.

   Self-check #1 (CG-1, audit item 6): `frozen_T1_refinement` takes `po_twin` and `dup_r12` as bare
   hypotheses; `Token_model.po_twin_derived` / `dup_r12_derived` proved them SEPARATELY. So "all green"
   did not, by itself, show the token structure DISCHARGES the RO-adapter obligations inside T1 — the
   mapping lived only in the assumption report. This file closes that gap: it declares the token-level
   commitments (the re-execution orientation `po k d`, the footprint/trap scope facts, same-static
   deps, the same-hart reader fact) and DERIVES `po_twin` + `dup_r12` from `Token_model`, then feeds
   them to `frozen_T1_refinement`. The result `frozen_T1_refinement_instantiated` has the SAME
   conclusion as the capstone but its RO-adapter premises are replaced by the more primitive token
   structure — so the po-twin / r12 obligations are now discharged INSIDE the theorem, not merely
   cross-referenced.

   HONESTY (unchanged): the token-level commitments themselves are the explicit research completion
   (resumed program order, the provisional/replay token structure); `footprint_read_not_in_trap` and
   `reader_after_d` are scope-register facts about the handler image, not RVWMO theorems; the fault-run
   consistency premises remain antecedents; none of this is human-verified (§9.4). Self-contained modulo
   T1_frozen_refinement + Token_model; 0 Admitted / 0 axioms (Print Assumptions). Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import RestartV.L1_abstract_erasure.
Require Import RestartV.Obs_final_state.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Rlift_mainmodel.
Require Import RestartV.Frozen_mainmodel.
Require Import RestartV.T1_frozen.
Require Import RestartV.Token_model.
Require Import RestartV.T1_frozen_refinement.
Import ListNotations.

Section T1Inst.

  Variable Event : Type.
  Variable eq_ev_dec : forall x y : Event, {x = y} + {x <> y}.
  Variable Byte Hart Value : Type.
  Variable gmo : Event -> Event -> Prop.
  Variable is_write is_read is_load is_store : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable wval : Event -> Byte -> Value.
  Variable same_addr addr data ctrl fence : Event -> Event -> Prop.
  Variable hart : Event -> Hart.
  Variable E0 : list Event.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable po poloc : Event -> Event -> Prop.
  Variables p q k d : Event.

  (* ---- the frozen-T1 capstone hypotheses (identical to T1_frozen_refinement, MINUS po_twin/dup_r12) ---- *)
  Hypothesis Hirr : forall e, In e E0 -> ~ gmo e e.
  Hypothesis Htr  : forall a b c, In a E0 -> In b E0 -> In c E0 -> gmo a b -> gmo b c -> gmo a c.
  Hypothesis Htot : forall a b, In a E0 -> In b E0 -> a <> b -> gmo a b \/ gmo b a.
  Hypothesis d_in : In d E0.
  Hypothesis d_w  : is_write d.
  Hypothesis k_in : In k E0.
  Hypothesis k_w  : is_write k.
  Hypothesis kd_ne : k <> d.
  Hypothesis keeper_before : gmo k d.
  Hypothesis p_in : In p E0.
  Hypothesis q_in : In q E0.
  Hypothesis Hdup : DupPair Event Byte Value is_write touches wval p q.
  Hypothesis Hro  : RO_K Event gmo po p q k.
  Hypothesis Hdpq : d = p \/ d = q.
  Hypothesis Hgamma : forall b, gamma_adj Event Byte is_write touches E0 gmo b p q.
  Hypothesis dup_val : forall b, touches d b -> wval k b = wval d b.
  Hypothesis rf_is_C4 : forall b r w, is_read r -> In r E0 -> rf w b r ->
      C4_source Event Byte is_write touches gmo po E0 b r w.
  Hypothesis rf_touches : forall w b r, rf w b r -> touches w b.
  Hypothesis rw_disjoint : forall e, is_read e -> is_write e -> False.
  Hypothesis hart_dk : hart d = hart k.
  Hypothesis Hadj : forall b, touches d b ->
      touches d b /\ touches k b /\
      (forall w, In w E0 -> is_write w -> touches w b -> ~ (gmo k w /\ gmo w d)).
  Hypothesis foot_dk : forall x, touches d x -> touches k x.
  Hypothesis rf_functional : forall w1 w2 x r, rf w1 x r -> rf w2 x r -> w1 = w2.

  (* ---- the TOKEN-LEVEL commitments that DISCHARGE po_twin (D4) and dup_r12 (D6) ---- *)
  (* re-execution orientation: keeper k = first attempt, program-order before the replay d *)
  Hypothesis po_trans : forall a b c, po a b -> po b c -> po a c.
  Hypothesis pkd : po k d.
  (* localized po-linearity: events po-before the replay are po-comparable to the first attempt *)
  Hypothesis po_total_before_d : forall e, e <> k -> po e d -> po e k \/ po k e.
  (* scope: a U-mode footprint read is never a trap-region event (handler does not touch the store footprint) *)
  Hypothesis footprint_read_not_in_trap :
    forall a x, is_read a -> touches a x -> touches d x -> ~ (po k a /\ po a d).
  (* d,k are occurrences of one static instruction ⇒ identical syntactic deps *)
  Hypothesis same_static_deps : forall e, (addr e k -> addr e d) /\ (data e k -> data e d).
  (* scope: a load that (in a dup_r12 obligation, hence on k's hart) observes the replay d is po-after it *)
  Hypothesis reader_after_d : forall bb b, po k b -> rf d bb b -> po d b.

  (* ---- DISCHARGE po_twin (D4) from Token_model.po_twin_derived ---- *)
  Lemma po_twin_wired :
    forall a b x, is_read a -> touches a x -> touches d x -> po a d -> po d b -> po a k /\ po k b.
  Proof.
    intros a b x Rd Tx Tdx Pad Pdb.
    (* the footprint premise `~ (po k a /\ po a d)` is convertible to `~ in_trap Event po d k a` *)
    exact (Token_model.po_twin_derived Event Byte po is_read is_write touches
             po_trans d k pkd k_w rw_disjoint po_total_before_d
             footprint_read_not_in_trap a b x Rd Tx Tdx Pad Pdb).
  Qed.

  (* ---- DISCHARGE dup_r12 (D6) from Token_model.dup_r12_derived ---- *)
  Lemma dup_r12_wired :
    forall a b bb, po a k -> po k b -> (addr a k \/ data a k) -> rf d bb b ->
      po a d /\ po d b /\ (addr a d \/ data a d).
  Proof.
    intros a b bb Hak Hkb Hdep Hrf.
    exact (Token_model.dup_r12_derived Event Byte po po_trans d k pkd rf addr data
             same_static_deps reader_after_d a b bb Hak Hkb Hdep Hrf).
  Qed.

  Let Cn := Clift_coherence.Cn Event Byte gmo is_write is_read touches E0 rf poloc d k.
  Let FRf := Frozen_mainmodel.FRf Event Byte Hart gmo is_write is_read is_load is_store touches
               same_addr addr data ctrl fence hart E0 rf po.
  Let Cf := Clift_coherence.Cf Event Byte gmo is_write is_read touches E0 rf poloc.

  (* ---- the capstone, with D4/D6 discharged from token structure INSIDE the theorem ---- *)
  Theorem frozen_T1_refinement_instantiated :
    (forall x, ~ clos_trans Event Cf x x) ->
    (forall x, ~ clos_trans Event FRf x x) ->
    exists (E_N : list Event) (rf_N : Event -> Byte -> Event -> Prop),
      E_N = L1_abstract_erasure.contract_carrier Event eq_ev_dec E0 d /\
      rf_N = L1_abstract_erasure.rf_retarget Event Byte d k rf /\
      (forall x, ~ clos_trans Event Cn x x) /\
      (forall x, ~ clos_trans Event
        (Rlift_mainmodel.Rn Event Byte Hart gmo is_write is_read touches hart E0 rf
          (Frozen_mainmodel.frozen_ppo_wit Event Byte is_write is_read is_load is_store touches
             same_addr addr data ctrl fence E0 rf po d k) d k) x x) /\
      L1_abstract_erasure.L1_consistent Event Byte is_write is_read touches gmo po E_N rf_N /\
      (forall r b w, In r E_N -> is_read r -> rf w b r ->
         exists w', rf_N w' b r /\ wval w' b = wval w b) /\
      (forall b w_f,
         co_max_of Event Byte gmo is_write touches (inE0 Event E0) b w_f ->
         exists w_n, co_max_of Event Byte gmo is_write touches (survivor Event E0 d) b w_n /\
                     wval w_f b = wval w_n b).
  Proof.
    intros Hcf Hfrf.
    exact (T1_frozen_refinement.frozen_T1_refinement Event eq_ev_dec Byte Hart Value gmo
             is_write is_read is_load is_store touches wval same_addr addr data ctrl fence hart E0 rf
             po poloc p q k d
             Hirr Htr Htot d_in d_w k_in k_w kd_ne keeper_before p_in q_in Hdup Hro Hdpq Hgamma
             dup_val rf_is_C4 rf_touches rw_disjoint hart_dk po_trans Hadj foot_dk
             po_twin_wired rf_functional dup_r12_wired Hcf Hfrf).
  Qed.

End T1Inst.
