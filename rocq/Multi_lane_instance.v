(* Multi_lane_instance.v — non-vacuity of the multi-lane iteration.
 *
 * Multi_lane.v proves that erasing a LIST of provisional duplicates preserves the load-value rule
 * and every read value. Those theorems are conditional on lanes_ok, which demands a keeper, a
 * re-execution orientation, and coherence-adjacency for every lane. A conditional theorem whose
 * premise is unsatisfiable proves nothing, so this file exhibits an execution that satisfies it.
 *
 * The instance is the smallest one with genuine multi-lane content: TWO provisional lanes, each
 * with its own keeper/duplicate pair on its own byte, and one observing read that sources BOTH
 * bytes from the duplicates. After the fold both sources are gone from the carrier, so the theorem
 * has to supply replacements. It does, the values it supplies are the ones the read saw, and the
 * replacements are the two keepers.
 *
 * Events:  0 keeper of lane A      1 duplicate of lane A   (byte 0, value 7)
 *          2 keeper of lane B      3 duplicate of lane B   (byte 1, value 9)
 *          4 the observing read
 *
 * Coherence and program order are both the numeric order, so in each lane the keeper precedes its
 * duplicate -- the re-execution orientation -- and no write sits coherence-between them.
 *
 * No Admitted, no axioms. Coq 8.15.
 *)

From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import RestartV.Multi_lane.

(* ------------------------------------------------------------------- the concrete execution *)

Definition IW (e : nat) : Prop := e <= 3.
Definition IR (e : nat) : Prop := e = 4.

Definition TCH (e b : nat) : Prop :=
  match e with
  | 0 | 1 => b = 0
  | 2 | 3 => b = 1
  | _     => b = 0 \/ b = 1
  end.

Definition WV (e b : nat) : nat :=
  match e with
  | 0 | 1 => 7
  | 2 | 3 => 9
  | _     => 0
  end.

Definition EE : list nat := [0; 1; 2; 3; 4].
Definition LS : list (lane nat) := [(0, 1); (2, 3)].

(* the read sees byte 0 from duplicate 1 and byte 1 from duplicate 3 -- both about to be erased *)
Definition RF (w b rd : nat) : Prop :=
  rd = 4 /\ ((b = 0 /\ w = 1) \/ (b = 1 /\ w = 3)).

(* --------------------------------------------------------- the model hypotheses, discharged *)

Lemma i_gmo_trans : forall x y z : nat, x < y -> y < z -> x < z.
Proof. lia. Qed.

Lemma i_gmo_total_w : forall x y : nat, IW x -> IW y -> x <> y -> x < y \/ y < x.
Proof. unfold IW; lia. Qed.

Lemma i_po_trans : forall x y z : nat, x < y -> y < z -> x < z.
Proof. lia. Qed.

(* ------------------------------------------------------------------- lanes_ok is inhabited *)

Lemma i_drop1 : drop nat Nat.eq_dec 1 EE = [0; 2; 3; 4].
Proof. reflexivity. Qed.

(* Lane A, against the full carrier. *)
Lemma i_laneA : lane_ok nat nat nat IW TCH WV lt lt EE (0, 1).
Proof.
  unfold lane_ok, EE, IW, TCH, WV.
  split; [simpl; left; reflexivity |].
  split; [discriminate |].
  split; [lia |].
  split; [intros b H; exact H |].
  split; [intros b H; reflexivity |].
  split; [lia |].
  split; [lia |].
  (* coherence-adjacency: no write can sit strictly between 0 and 1 *)
  intros z Hin Hw Hn0 Hn1 [H1 H2]. lia.
Qed.

(* Lane B, against the carrier from which lane A's duplicate has already been removed. *)
Lemma i_laneB :
  lane_ok nat nat nat IW TCH WV lt lt (drop nat Nat.eq_dec 1 EE) (2, 3).
Proof.
  rewrite i_drop1. unfold lane_ok, IW, TCH, WV.
  split; [simpl; right; left; reflexivity |].
  split; [discriminate |].
  split; [lia |].
  split; [intros b H; exact H |].
  split; [intros b H; reflexivity |].
  split; [lia |].
  split; [lia |].
  intros z Hin Hw Hn2 Hn3 [H1 H2]. lia.
Qed.

Lemma i_lanes_ok : lanes_ok nat Nat.eq_dec nat nat IW TCH WV lt lt LS EE.
Proof.
  unfold LS. simpl.
  split; [exact i_laneA |].
  split; [exact i_laneB | exact I].
Qed.

(* --------------------------------------------------------------- the load-value rule holds *)

Lemma i_rf_1_0 : RF 1 0 4.
Proof. unfold RF. split; [reflexivity | left; split; reflexivity]. Qed.

Lemma i_rf_3_1 : RF 3 1 4.
Proof. unfold RF. split; [reflexivity | right; split; reflexivity]. Qed.

Lemma i_nrf_3_0 : ~ RF 3 0 4.
Proof. unfold RF. intros [_ [[_ H] | [H _]]]; discriminate. Qed.

Lemma i_nrf_1_1 : ~ RF 1 1 4.
Proof. unfold RF. intros [_ [[H _] | [_ H]]]; discriminate. Qed.

Lemma i_uniq : forall (b rd w1 w2 : nat), RF w1 b rd -> RF w2 b rd -> w1 = w2.
Proof.
  unfold RF. intros b rd w1 w2 [_ H1] [_ H2].
  destruct H1 as [[Hb1 Hw1] | [Hb1 Hw1]]; destruct H2 as [[Hb2 Hw2] | [Hb2 Hw2]];
    subst; try reflexivity; discriminate.
Qed.

Lemma i_C4 : C4 nat nat IW IR TCH lt lt EE RF.
Proof.
  unfold C4, cand, RF, EE, IW, TCH.
  intros b rd w Hrd Hin [Hrd4 Hcase].
  destruct Hcase as [[Hb Hw] | [Hb Hw]]; subst b; subst w; subst rd.
  - (* byte 0 is sourced from duplicate 1 *)
    split.
    + split; [simpl; right; left; reflexivity |].
      split; [lia |].
      split; [reflexivity | left; lia].
    + intros w' [Hin' [Hw' [Ht' _]]].
      (* a write that touches byte 0 is 0 or 1, so it is the source or coherence-earlier *)
      destruct w' as [| [| [| [| w'']]]]; simpl in Ht', Hw';
        [right; lia | left; reflexivity | discriminate | discriminate | lia].
  - (* byte 1 is sourced from duplicate 3 *)
    split.
    + split; [simpl; right; right; right; left; reflexivity |].
      split; [lia |].
      split; [reflexivity | left; lia].
    + intros w' [Hin' [Hw' [Ht' _]]].
      destruct w' as [| [| [| [| w'']]]]; simpl in Ht', Hw';
        [discriminate | discriminate | right; lia | left; reflexivity | lia].
Qed.

(* ------------------------------------------------------------------------------ the payoff *)

(* Both duplicates really are gone from the carrier the fold produces. *)
Lemma i_carrier : erase_all nat Nat.eq_dec LS EE = [0; 2; 4].
Proof. reflexivity. Qed.

(* The load-value rule survives the two-lane fold. *)
Theorem i_C4_survives :
  C4 nat nat IW IR TCH lt lt
     (erase_all nat Nat.eq_dec LS EE) (rf_all nat nat LS RF).
Proof.
  apply (erase_all_preserves_C4 nat Nat.eq_dec nat nat IW IR TCH WV lt lt
           i_gmo_trans i_gmo_total_w i_po_trans);
    [exact i_C4 | exact i_lanes_ok].
Qed.

(* The read still sees value 7 at byte 0 after both duplicates are erased. *)
Theorem i_value_byte0 :
  exists w', rf_all nat nat LS RF w' 0 4 /\ WV w' 0 = 7 /\ TCH w' 0.
Proof.
  destruct (erase_all_preserves_values nat Nat.eq_dec nat nat IW TCH WV lt lt LS EE RF
              i_lanes_ok i_uniq 0 4 1 i_rf_1_0 eq_refl)
    as [w' [Hrf [Hval Htch]]].
  exists w'. split; [exact Hrf |]. split; [exact Hval | exact Htch].
Qed.

(* The same for the second lane's byte: value 9 survives the same fold. *)
Theorem i_value_byte1 :
  exists w', rf_all nat nat LS RF w' 1 4 /\ WV w' 1 = 9 /\ TCH w' 1.
Proof.
  destruct (erase_all_preserves_values nat Nat.eq_dec nat nat IW TCH WV lt lt LS EE RF
              i_lanes_ok i_uniq 1 4 3 i_rf_3_1 eq_refl)
    as [w' [Hrf [Hval Htch]]].
  exists w'. split; [exact Hrf |]. split; [exact Hval | exact Htch].
Qed.

(* And the replacement sources are exactly the two keepers, both of which survived the fold. *)
Theorem i_sources_are_keepers :
  rf_all nat nat LS RF 0 0 4 /\ rf_all nat nat LS RF 2 1 4
  /\ In 0 (erase_all nat Nat.eq_dec LS EE) /\ In 2 (erase_all nat Nat.eq_dec LS EE).
Proof.
  unfold LS, EE. simpl.
  split.
  - (* byte 0: lane B leaves it alone, lane A moved it to keeper 0 *)
    left. split.
    + right. split; [exact i_rf_1_0 | reflexivity].
    + intros [[H _] | [_ H]]; [apply i_nrf_3_0; exact H | discriminate].
  - split.
    + (* byte 1: lane A left it alone, lane B moved it to keeper 2 *)
      right. split; [| reflexivity].
      left. split; [exact i_rf_3_1 | exact i_nrf_1_1].
    + split; simpl; auto.
Qed.
