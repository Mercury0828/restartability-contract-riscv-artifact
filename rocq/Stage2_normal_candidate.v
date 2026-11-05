(* Stage2_normal_candidate.v — RESTART-V Stage-2 **LAYER 3 ONLY**: the STRUCTURAL normal-candidate
   construction.  Fully abstract (a Section over Variables), like `Ctx_erasure.v` — this is the
   ∀ version, deliberately NOT built on the concrete CG-2 model.

   ===================================================================================================
   WHAT THIS FILE IS
   ===================================================================================================
   `Ctx_erasure.general_ctx_erasure` gives, for ANY contracted carrier, a trap-free RVWMO-consistent
   memory KERNEL `EK` with the same memory projection.  What it does NOT give is a member of the
   no-fault CANDIDATE class: the retained lane writes still carry first/replay phase labels, the fault
   run's denied PMP check is still present, and the successful normal checks are missing.

   THIS FILE SUPPLIES EXACTLY THAT STRUCTURAL STEP (GPT Pro's "Layer 3"), and nothing more:
     - it relabels every retained event to the `once` phase (`phase_N` is constantly `PhOnce`);
     - it DROPS the fault run's check events (`mem_kernel` = `EK` minus `is_chk`);
     - it GENERATES one check event `NChk l` per frozen lane, asserted successful by definition;
     - it shows the RVWMO relations (`gmo`, `rf`, `po-loc`, hence `Clift_coherence.Cf`) and the memory
       projection (`Obs_final_state.co_max_of`) transport along the injection `NKeep`.
   It is purely combinatorial: it needs NO operational semantics.

   ===================================================================================================
   WHAT THIS FILE DOES **NOT** PROVE — READ THIS BEFORE QUOTING ANYTHING BELOW
   ===================================================================================================
   1. **It does NOT prove `StateWF`** (Stage-2 Layer 4).  There is here:
        * NO state chain,
        * NO adjacent-state continuity,
        * NO decoding or token conformance,
        * NO precise-state condition,
        * NO final-state construction.
      In particular the no-fault initial PMP state is *already repaired*, so the fault run's pre/post
      states CANNOT simply be copied onto this carrier.  Reconstructing the normal state chain is
      exactly the remaining work, and GPT Pro judges it the BULK of general Stage-2.  Nothing in this
      file makes progress on it.

   2. `Cand_N_struct` is OUR **STRUCTURAL RENDERING** of the no-fault candidate class (all events
      `once`; exactly one `once` lane write per lane; a successful normal check per lane; no denied
      check surviving).  It is NOT the full D-a `Cand_N`, which is stated over the OPERATIONAL model
      together with `StateWF`.  `Cand_N_struct` is strictly weaker and must never be cited as `Cand_N`.

   3. The generated check events `NChk l` are **CONSTRUCTED BY US** and asserted successful
      **BY DEFINITION** (`chk_ok_N (NChk _) := True`).  That such a check *would actually succeed*
      against the repaired PMP state is an OPERATIONAL fact belonging to Layer 4 and is **NOT
      established here**.  `chk_ok_N` is a label we paint on, not a verdict we computed.

   4. `kernel_one_write_per_lane` and `chk_nonmem` are **NAMED ANTECEDENTS** — Section Hypotheses,
      i.e. ∀-bound premises of the theorems below.  They are properties of the Stage-1 duplicate
      erasure and of the frozen event grammar respectively, and they are NOT results proved here.
      "0 axioms" means nothing is smuggled in past the interface, NOT that these are discharged.

   5. Therefore the ONLY honest reading of `stage2_normal_candidate` is:
        "GIVEN a trap-free memory kernel (plus the named antecedents), there is a STRUCTURALLY normal
         candidate carrying the same RVWMO relations and the same memory projection."
      Composed with `Ctx_erasure.general_ctx_erasure`, this STILL FALLS SHORT of
        "there exists a no-fault EXECUTION"
      until Layer 4 (`StateWF`) lands.

   ===================================================================================================
   EXTRA INTERFACE HYPOTHESIS BEYOND THE COMMISSIONED LIST — FLAGGED
   ===================================================================================================
       lane_write_is_write : forall e, is_lane_write e -> is_write e
   The commissioned interface declares `is_lane_write` and `is_chk` as unrelated predicates, and
   `chk_nonmem` only says checks are non-memory.  To place the surviving lane write of a lane INTO
   `mem_kernel` (i.e. to know it is not filtered out as a check) we must know a lane write is not a
   check, and the only available route is: a lane write IS a memory write, and by `chk_nonmem` a check
   is not.  `lane_write_is_write` is a basic typing fact of the frozen event grammar (a vector-store
   lane write is an RVWMO write), NOT a fresh contract commitment — but it IS an added hypothesis and
   it DOES appear in the printed type of the headline.  Flagged here and in the report.

   NOTE on the commissioned-but-unused interface items.  `poloc_touches`, `rf_src_write` and
   `rf_tgt_read` are declared for interface fidelity with `Ctx_erasure.v` but turn out to be UNUSED:
   the structural construction refutes the `NChk` endpoints of every `Cf` disjunct by the SHAPE of
   `gmo_N` / `rf_N` / `poloc_N` / `is_write_N` / `is_read_N` (all `False` on `NChk`), so no RVWMO
   typing fact is needed.  Likewise `phase`, `chk_ok` and a decidable equality on `Event` are not
   needed: `phase_N` and `chk_ok_N` are defined outright, and no proof here decides equality on `NEv`
   (so the anticipated `nev_eq_dec` was DROPPED rather than assumed).  Being unused, none of these
   appear in the printed type of any theorem.

   Reuses the EXISTING abstract relations with NO re-definition: `Clift_coherence.Cf` instantiated at
   BOTH universes (`Event` and `NEv`), and `Obs_final_state.co_max_of` likewise.
   0 Admitted / 0 axioms (`Print Assumptions stage2_normal_candidate`).  Coq 8.15. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import RestartV.Clift_coherence.
Require Import RestartV.Obs_final_state.
Import ListNotations.

Section Stage2Normal.

  (* ===================================================================== *)
  (* 0.  The abstract interface                                             *)
  (* ===================================================================== *)

  Variable Event Byte Lane : Type.
  Variable gmo poloc : Event -> Event -> Prop.
  Variable is_read is_write : Event -> Prop.
  Variable touches : Event -> Byte -> Prop.
  Variable rf : Event -> Byte -> Event -> Prop.
  Variable EK : list Event.        (* the trap-free memory kernel handed over by Ctx_erasure *)

  (* phase labels and the frozen fragment's event roles *)
  Inductive Phase := PhFirst | PhReplay | PhOnce.
  Variable phase : Event -> Phase.          (* declared for fidelity; UNUSED (see header) *)
  Variable lane  : Event -> Lane.
  Variable is_lane_write : Event -> Prop.   (* a vector-store lane write *)
  Variable is_chk : Event -> Prop.          (* a PMP check event (non-memory) *)
  Variable chk_ok : Event -> Prop.          (* a SUCCESSFUL check; declared for fidelity, UNUSED *)
  Variable chk_dec : forall e, {is_chk e} + {~ is_chk e}.
  Variable lanes : list Lane.               (* the frozen VL lanes *)

  (* ---- NAMED ANTECEDENTS (see header item 4): properties of the Stage-1 erasure and of the
          frozen event grammar.  NOT results. ---- *)

  (* after duplicate erasure exactly one lane write per lane survives in the kernel *)
  Hypothesis kernel_one_write_per_lane :
    forall l, In l lanes ->
      exists w, In w EK /\ is_lane_write w /\ lane w = l /\
                (forall w', In w' EK -> is_lane_write w' -> lane w' = l -> w' = w).

  (* checks are NON-memory events (so they never enter the RVWMO relations) *)
  Hypothesis chk_nonmem :
    forall e, is_chk e -> ~ is_read e /\ ~ is_write e /\ (forall b, ~ touches e b).

  (* EXTRA, beyond the commissioned list — FLAGGED in the header. *)
  Hypothesis lane_write_is_write : forall e, is_lane_write e -> is_write e.

  (* Commissioned RVWMO typing facts.  Declared for interface fidelity with Ctx_erasure.v; they turn
     out to be UNUSED by every theorem below (see header) and hence appear in no printed type. *)
  Hypothesis poloc_touches : forall x y, poloc x y -> exists b, touches x b /\ touches y b.
  Hypothesis rf_src_write  : forall w b r, rf w b r -> is_write w.
  Hypothesis rf_tgt_read   : forall w b r, rf w b r -> is_read r.

  (* ===================================================================== *)
  (* 1.  The normal event universe and carrier — CONSTRUCTED, not assumed   *)
  (* ===================================================================== *)

  Inductive NEv :=
  | NKeep : Event -> NEv        (* a retained kernel MEMORY event, relabelled to the `once` phase *)
  | NChk  : Lane  -> NEv.       (* the GENERATED successful normal check for a lane (header item 3) *)

  (* the kernel with the fault run's check events removed *)
  Definition mem_kernel : list Event :=
    filter (fun e => if chk_dec e then false else true) EK.

  Definition EN' : list NEv := map NKeep mem_kernel ++ map NChk lanes.

  (* labels: EVERYTHING in the normal candidate is `once`; the checks are the generated successful
     ones.  `chk_ok_N` is a DEFINITION, i.e. a label we paint on — see header item 3. *)
  Definition phase_N (n : NEv) : Phase := PhOnce.
  Definition lane_N  (n : NEv) : Lane  := match n with NKeep e => lane e | NChk l => l end.
  Definition is_lane_write_N (n : NEv) : Prop :=
    match n with NKeep e => is_lane_write e | NChk _ => False end.
  Definition is_chk_N (n : NEv) : Prop := match n with NKeep _ => False | NChk _ => True end.
  Definition chk_ok_N (n : NEv) : Prop := match n with NKeep _ => False | NChk _ => True end.
  Definition is_read_N  (n : NEv) : Prop := match n with NKeep e => is_read e  | NChk _ => False end.
  Definition is_write_N (n : NEv) : Prop := match n with NKeep e => is_write e | NChk _ => False end.
  Definition touches_N (n : NEv) (b : Byte) : Prop :=
    match n with NKeep e => touches e b | NChk _ => False end.
  Definition gmo_N (m n : NEv) : Prop :=
    match m, n with NKeep a, NKeep b => gmo a b | _, _ => False end.
  Definition poloc_N (m n : NEv) : Prop :=
    match m, n with NKeep a, NKeep b => poloc a b | _, _ => False end.
  Definition rf_N (m : NEv) (b : Byte) (n : NEv) : Prop :=
    match m, n with NKeep w, NKeep r => rf w b r | _, _ => False end.

  (* ===================================================================== *)
  (* 2.  Membership bridge                                                  *)
  (* ===================================================================== *)

  Lemma In_mem_kernel_iff : forall e, In e mem_kernel <-> (In e EK /\ ~ is_chk e).
  Proof.
    intros e. unfold mem_kernel. rewrite filter_In. split.
    - intros [Hin Hb]. split; [exact Hin|].
      destruct (chk_dec e) as [Hc|Hnc]; [discriminate Hb | exact Hnc].
    - intros [Hin Hnc]. split; [exact Hin|].
      destruct (chk_dec e) as [Hc|_]; [exfalso; apply Hnc; exact Hc | reflexivity].
  Qed.

  Lemma mem_kernel_sub : forall e, In e mem_kernel -> In e EK.
  Proof. intros e H. apply In_mem_kernel_iff in H. destruct H as [H _]; exact H. Qed.

  (* THEOREM 3 of the design: the membership bridge. *)
  Lemma In_NKeep_iff : forall e, In (NKeep e) EN' <-> (In e EK /\ ~ is_chk e).
  Proof.
    intros e. unfold EN'. rewrite in_app_iff. split.
    - intros [H | H].
      + apply in_map_iff in H. destruct H as [x [Heq Hin]].
        injection Heq as Heq. subst x. apply In_mem_kernel_iff; exact Hin.
      + apply in_map_iff in H. destruct H as [l [Heq _]]. discriminate Heq.
    - intros H. left. apply in_map_iff. exists e. split; [reflexivity|].
      apply In_mem_kernel_iff; exact H.
  Qed.

  Lemma NKeep_in_mem_kernel : forall e, In (NKeep e) EN' -> In e mem_kernel.
  Proof. intros e H. apply In_mem_kernel_iff. apply In_NKeep_iff. exact H. Qed.

  Lemma mem_kernel_NKeep_in : forall e, In e mem_kernel -> In (NKeep e) EN'.
  Proof. intros e H. apply In_NKeep_iff. apply In_mem_kernel_iff. exact H. Qed.

  Lemma NChk_in : forall l, In l lanes -> In (NChk l) EN'.
  Proof.
    intros l H. unfold EN'. apply in_or_app. right. apply in_map. exact H.
  Qed.

  (* a lane write is never a check, so it survives the check filter *)
  Lemma lane_write_not_chk : forall e, is_lane_write e -> ~ is_chk e.
  Proof.
    intros e Hlw Hc. destruct (chk_nonmem e Hc) as [_ [Hnw _]].
    apply Hnw. apply lane_write_is_write. exact Hlw.
  Qed.

  (* ===================================================================== *)
  (* 3.  The STRUCTURAL no-fault candidate predicate                        *)
  (*     (header item 2: this is NOT the full D-a `Cand_N`)                 *)
  (* ===================================================================== *)

  Definition Cand_N_struct : Prop :=
    (* every event is `once` — no first/replay phase survives *)
    (forall n, In n EN' -> phase_N n = PhOnce)
    (* exactly one once lane-write per lane *)
    /\ (forall l, In l lanes ->
          exists n, In n EN' /\ is_lane_write_N n /\ lane_N n = l /\
                    (forall n', In n' EN' -> is_lane_write_N n' -> lane_N n' = l -> n' = n))
    (* every lane has a successful normal check (GENERATED by us — header item 3) *)
    /\ (forall l, In l lanes -> exists c, In c EN' /\ is_chk_N c /\ chk_ok_N c /\ lane_N c = l)
    (* NO denied check survives *)
    /\ (forall c, In c EN' -> is_chk_N c -> chk_ok_N c).

  (* THEOREM 1 *)
  Theorem EN'_Cand_N_struct : Cand_N_struct.
  Proof.
    unfold Cand_N_struct. split.
    - (* every event is `once` *)
      intros n _. reflexivity.
    - split.
      + (* exactly one once lane-write per lane *)
        intros l Hl.
        destruct (kernel_one_write_per_lane l Hl) as [w [Hin [Hlw [Hlane Huniq]]]].
        exists (NKeep w). split.
        * apply In_NKeep_iff. split; [exact Hin | apply lane_write_not_chk; exact Hlw].
        * split; [exact Hlw|]. split; [exact Hlane|].
          intros n' Hin' Hlw' Hlane'.
          destruct n' as [e'|l'].
          -- f_equal. apply Huniq.
             ++ apply mem_kernel_sub. apply NKeep_in_mem_kernel. exact Hin'.
             ++ exact Hlw'.
             ++ exact Hlane'.
          -- exfalso. exact Hlw'.
      + split.
        * (* every lane has a successful normal check *)
          intros l Hl. exists (NChk l).
          split; [apply NChk_in; exact Hl|].
          split; [exact I|]. split; [exact I | reflexivity].
        * (* no denied check survives *)
          intros c _ Hchk. destruct c as [e|l]; [ exfalso; exact Hchk | exact I ].
  Qed.

  (* ===================================================================== *)
  (* 4.  Relation transport — TRUE BY DEFINITION, stated so it is quotable  *)
  (* ===================================================================== *)

  (* THEOREM 2 *)
  Theorem transport_gmo : forall a b, gmo_N (NKeep a) (NKeep b) <-> gmo a b.
  Proof. intros a b. split; intro H; exact H. Qed.

  Theorem transport_rf : forall w b r, rf_N (NKeep w) b (NKeep r) <-> rf w b r.
  Proof. intros w b r. split; intro H; exact H. Qed.

  Theorem transport_poloc : forall a b, poloc_N (NKeep a) (NKeep b) <-> poloc a b.
  Proof. intros a b. split; intro H; exact H. Qed.

  (* ===================================================================== *)
  (* 5.  Per-location consistency transfers                                 *)
  (* ===================================================================== *)

  Definition CfN := Clift_coherence.Cf NEv Byte gmo_N is_write_N is_read_N touches_N EN' rf_N poloc_N.
  Definition CfK := Clift_coherence.Cf Event Byte gmo is_write is_read touches mem_kernel rf poloc.

  (* No `Cf` edge can start at a generated check: every disjunct demands a write / a read / an rf
     source / a po-loc source, and all of those are `False` on `NChk`. *)
  Lemma CfN_NChk_src : forall l n, ~ CfN (NChk l) n.
  Proof.
    intros l n H. unfold CfN, Clift_coherence.Cf in H.
    destruct H as [[bb Hco] | [ [bb [Hrm _]] | [ [bb Hrf] | Hpl ] ] ].
    - unfold Clift_coherence.co_flt, Clift_coherence.coOn in Hco.
      destruct Hco as [_ [_ [W1 _]]]. exact W1.
    - exact Hrm.
    - exact Hrf.
    - exact Hpl.
  Qed.

  (* ... nor end at one. *)
  Lemma CfN_NKeep_NChk : forall a l, ~ CfN (NKeep a) (NChk l).
  Proof.
    intros a l H. unfold CfN, Clift_coherence.Cf in H.
    destruct H as [[bb Hco] | [ [bb [_ Hfr]] | [ [bb Hrf] | Hpl ] ] ].
    - unfold Clift_coherence.co_flt, Clift_coherence.coOn in Hco.
      destruct Hco as [_ [_ [_ [W2 _]]]]. exact W2.
    - unfold Clift_coherence.fr_flt in Hfr. destruct Hfr as [w1 [_ Hco]].
      unfold Clift_coherence.co_flt, Clift_coherence.coOn in Hco.
      destruct Hco as [_ [_ [_ [W2 _]]]]. exact W2.
    - exact Hrf.
    - exact Hpl.
  Qed.

  (* THEOREM 4a: every normal per-location edge REFLECTS to a kernel per-location edge. *)
  Theorem edge_reflect :
    forall m n, CfN m n -> exists a b, m = NKeep a /\ n = NKeep b /\ CfK a b.
  Proof.
    intros m n H.
    destruct m as [a|la]; [ | exfalso; exact (CfN_NChk_src la n H) ].
    destruct n as [b|lb]; [ | exfalso; exact (CfN_NKeep_NChk a lb H) ].
    exists a, b. split; [reflexivity|]. split; [reflexivity|].
    unfold CfN, Clift_coherence.Cf in H. unfold CfK, Clift_coherence.Cf.
    destruct H as [[bb Hco] | [ [bb [Hrm Hfr]] | [ [bb Hrf] | Hpl ] ] ].
    - (* co *)
      left. exists bb.
      unfold Clift_coherence.co_flt, Clift_coherence.coOn, Clift_coherence.inE0 in Hco.
      destruct Hco as [I1 [I2 [W1 [W2 [T1 [T2 G]]]]]].
      unfold Clift_coherence.co_flt, Clift_coherence.coOn, Clift_coherence.inE0.
      split; [apply NKeep_in_mem_kernel; exact I1|].
      split; [apply NKeep_in_mem_kernel; exact I2|].
      split; [exact W1|]. split; [exact W2|].
      split; [exact T1|]. split; [exact T2|]. exact G.
    - (* fr: the rf source must itself be an NKeep, since rf_N is False off the NKeep diagonal *)
      right; left. exists bb. split; [exact Hrm|].
      unfold Clift_coherence.fr_flt in Hfr. destruct Hfr as [w1 [Hrf1 Hco]].
      destruct w1 as [u|lu]; [ | exfalso; exact Hrf1 ].
      unfold Clift_coherence.fr_flt. exists u. split; [exact Hrf1|].
      unfold Clift_coherence.co_flt, Clift_coherence.coOn, Clift_coherence.inE0 in Hco.
      destruct Hco as [I1 [I2 [W1 [W2 [T1 [T2 G]]]]]].
      unfold Clift_coherence.co_flt, Clift_coherence.coOn, Clift_coherence.inE0.
      split; [apply NKeep_in_mem_kernel; exact I1|].
      split; [apply NKeep_in_mem_kernel; exact I2|].
      split; [exact W1|]. split; [exact W2|].
      split; [exact T1|]. split; [exact T2|]. exact G.
    - (* rf *)
      right; right; left. exists bb. exact Hrf.
    - (* po-loc *)
      right; right; right. exact Hpl.
  Qed.

  Lemma ctN_reflect : forall m n, clos_trans NEv CfN m n ->
    exists a b, m = NKeep a /\ n = NKeep b /\ clos_trans Event CfK a b.
  Proof.
    intros m n H. induction H as [m n Hstep | m y n _ IH1 _ IH2].
    - destruct (edge_reflect m n Hstep) as [a [b [Hm [Hn Hc]]]].
      exists a, b. split; [exact Hm|]. split; [exact Hn|]. apply t_step; exact Hc.
    - destruct IH1 as [a [b1 [Hm [Hy1 Hc1]]]].
      destruct IH2 as [b2 [c [Hy2 [Hn Hc2]]]].
      rewrite Hy1 in Hy2. injection Hy2 as Hy2. subst b2.
      exists a, c. split; [exact Hm|]. split; [exact Hn|].
      exact (t_trans Event CfK a b1 c Hc1 Hc2).
  Qed.

  (* THEOREM 4b *)
  Theorem CfN_acyclic :
    (forall x, ~ clos_trans Event CfK x x) -> (forall n, ~ clos_trans NEv CfN n n).
  Proof.
    intros Hacyc n Hcyc.
    destruct (ctN_reflect n n Hcyc) as [a [b [Hn1 [Hn2 Hc]]]].
    rewrite Hn1 in Hn2. injection Hn2 as Hn2. subst b.
    exact (Hacyc a Hc).
  Qed.

  (* ===================================================================== *)
  (* 6.  Memory projection preserved                                        *)
  (* ===================================================================== *)

  (* THEOREM 5 *)
  Theorem transport_co_max : forall b w,
    Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e mem_kernel) b w <->
    Obs_final_state.co_max_of NEv Byte gmo_N is_write_N touches_N (fun n => In n EN') b (NKeep w).
  Proof.
    intros b w. unfold Obs_final_state.co_max_of. split.
    - intros [Hw [Ht [Hin Hmax]]].
      split; [exact Hw|]. split; [exact Ht|].
      split; [apply mem_kernel_NKeep_in; exact Hin|].
      intros n' Hin' Hw' Ht'.
      destruct n' as [e'|l']; [ | exfalso; exact Hw' ].
      destruct (Hmax e' (NKeep_in_mem_kernel e' Hin') Hw' Ht') as [Heq | Hg].
      + left. f_equal. exact Heq.
      + right. exact Hg.
    - intros [Hw [Ht [Hin Hmax]]].
      split; [exact Hw|]. split; [exact Ht|].
      split; [apply NKeep_in_mem_kernel; exact Hin|].
      intros w' Hmk Hw' Ht'.
      destruct (Hmax (NKeep w') (mem_kernel_NKeep_in w' Hmk) Hw' Ht') as [Heq | Hg].
      + left. injection Heq as Heq. exact Heq.
      + right. exact Hg.
  Qed.

  (* ===================================================================== *)
  (* 7.  HEADLINE                                                           *)
  (* ===================================================================== *)

  (* HONEST READING (see header):  GIVEN a trap-free memory kernel and the named antecedents, there
     is a STRUCTURALLY normal candidate carrying the same RVWMO per-location relation and the same
     memory projection.  This is NOT "there exists a no-fault EXECUTION": `StateWF` (Layer 4) is not
     touched, `Cand_N_struct` is not the full D-a `Cand_N`, and the generated `NChk` events are
     asserted successful by definition, not shown to succeed against the repaired PMP state. *)
  Theorem stage2_normal_candidate :
    Cand_N_struct
    /\ ((forall x, ~ clos_trans Event CfK x x) -> (forall n, ~ clos_trans NEv CfN n n))
    /\ (forall a b, gmo_N (NKeep a) (NKeep b) <-> gmo a b)
    /\ (forall w b r, rf_N (NKeep w) b (NKeep r) <-> rf w b r)
    /\ (forall b w,
          Obs_final_state.co_max_of Event Byte gmo is_write touches (fun e => In e mem_kernel) b w
          <-> Obs_final_state.co_max_of NEv Byte gmo_N is_write_N touches_N
                (fun n => In n EN') b (NKeep w)).
  Proof.
    split; [ exact EN'_Cand_N_struct | ].
    split; [ exact CfN_acyclic | ].
    split; [ exact transport_gmo | ].
    split; [ exact transport_rf | ].
    exact transport_co_max.
  Qed.

End Stage2Normal.
