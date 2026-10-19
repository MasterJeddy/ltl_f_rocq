From LTL_F_Project Require Import ltl_f.
From LTL_F_Project Require Import ngbw.
From LTL_F_Project Require Import utils.
From LTL_F_Project Require Import proof2.
From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Streams.
From Stdlib Require Import Arith.
From Stdlib Require Import Classical.

Import ListNotations.
Open Scope R_scope.

Section until_lemmas.

  Variables AP F : Set.
  Variable f_to_f : F -> (list UnitInterval -> UnitInterval).

  Local Notation sat_val := (sat_val AP F f_to_f).
  Local Notation possible_statsfaction_values  := ( possible_statsfaction_values AP F f_to_f).

  Ltac destruct_keep b :=
    tryif is_var b then destruct b
    else let Heq := fresh "Heq" in destruct b eqn:Heq.

  Ltac split_matches :=
    match goal with
    | |- context [match ?b with _ => _ end] => destruct_keep b
    | H : context [match ?b with _ => _ end] |- _ => destruct_keep b
    end.

    Ltac crush :=
     let sintution := simpl in *; intuition ; try subst ; try split_matches ; try congruence in
     let rewriter := try autorewrite with core in * in
     (sintution ; rewriter ; sintution ; rewriter ; sintution ; try lia ; try eauto).

  Lemma until_is_achieved_eq : forall (sv: Computation AP -> ltl_f_expr AP F -> UnitInterval) c e1 e2 v,
    until_is_achieved AP F sv c e1 e2 v =
    if ClassicalEpsilon.excluded_middle_informative
      (exists i : nat,
         until_candidate_le_e2_at_i AP F sv c v e2 i /\
         until_candidate_eq_e2_at_i_or_e1_before_i AP F sv c v e2 i e1 /\
         until_candidate_le_all_e1_before_i AP F sv c v e1 i)
    then true
    else false.
     crush.
  Qed.

  Lemma until_candidates_eq : forall e1 e2, until_candidates AP F f_to_f e1 e2 = 
    possible_statsfaction_values e1 ++ possible_statsfaction_values e2 .
    crush.
  Qed.

  Lemma proof2_In : forall (e : ltl_f_expr AP F) (c : Computation AP),
    In (sat_val c e) (possible_statsfaction_values e).
   intros; apply proof2. 
  Qed.

  Lemma nil_no_In : forall A (l : list A) (x : A), l = [] -> In x l -> False.
    crush.
  Qed.

  Section until_is_achieved_iff.
    Hint Rewrite until_is_achieved_eq : core.

    (* Used to convert between until_is_achieved = true and the it's condetions *)
    Lemma until_is_achieved_iff : forall (sv: Computation AP -> ltl_f_expr AP F -> UnitInterval) c e1 e2 v,
      until_is_achieved AP F sv c e1 e2 v = true <->
      exists i : nat, 
        until_candidate_le_e2_at_i AP F sv c v e2 i /\
        until_candidate_eq_e2_at_i_or_e1_before_i AP F sv c v e2 i e1 /\
        until_candidate_le_all_e1_before_i AP F sv c v e1 i.
      crush.
    Qed.
  End until_is_achieved_iff.

  Section until_achieved_at_0.
    Hint Rewrite nth_tail_0 : core.
    Hint Resolve Rle_refl : core.

    Lemma until_achieved_at_0 : forall c e1 e2, until_is_achieved AP F sat_val c e1 e2 (sat_val c e2) = true.
      intros ;  rewrite until_is_achieved_iff ; exists O ; crush.
    Qed.
  End until_achieved_at_0.


  Lemma sat_val_until_eq : forall c e1 e2,
    sat_val c (UNTIL AP F e1 e2) =
    match filter (until_is_achieved AP F sat_val c e1 e2) (until_candidates AP F f_to_f e1 e2) with
    | [] => zero
    | x :: xs => fold_left unitinterval_max xs x
    end.
    crush. 
  Qed.

  Section sat_val_until_in_candidates_e2.
    Hint Rewrite until_candidates_eq  : core.
    Hint Resolve in_or_app : core.
    Hint Resolve proof2_In : core.

    Lemma sat_val_until_in_candidates_e2 : forall c e1 e2,
      In (sat_val c e2) (until_candidates AP F f_to_f e1 e2).
      crush.
    Qed.
  End sat_val_until_in_candidates_e2.


  Section sat_val_e2_at_c_satisfies_until_is_achieved.
    Hint Resolve until_achieved_at_0 : core.
    Hint Resolve sat_val_until_in_candidates_e2 : core.
    Hint Rewrite filter_In : core.

    Lemma sat_val_e2_at_c_satisfies_until_is_achieved : forall c e1 e2,
      In (sat_val c e2) (filter (until_is_achieved AP F sat_val c e1 e2) (until_candidates AP F f_to_f e1 e2)).
      crush.
    Qed.
  End sat_val_e2_at_c_satisfies_until_is_achieved.

  Section sat_val_until_nonempty.
    Hint Resolve nil_no_In : core.
    Hint Resolve sat_val_e2_at_c_satisfies_until_is_achieved : core.

    Lemma sat_val_until_nonempty : forall c e1 e2,
      filter (until_is_achieved AP F sat_val c e1 e2) (until_candidates AP F f_to_f e1 e2) <> [].
      crush.
    Qed.
  End sat_val_until_nonempty.

  Hint Resolve fold_left_max_upper_bound : core.

  Lemma sat_val_e2_le_until : forall c e1 e2,
    proj1_sig (sat_val c e2) <= proj1_sig (sat_val c (UNTIL AP F e1 e2)).
    intros c e1 e2.
    pose proof (sat_val_e2_at_c_satisfies_until_is_achieved c e1 e2).
    crush.
  Qed.

  Hint Rewrite sat_val_until_eq : core.
  Hint Resolve sat_val_until_nonempty : core.

  (* Continue here *)
  Lemma sat_val_until_achieved : forall c e1 e2,
    until_is_achieved AP F sat_val c e1 e2 (sat_val c (UNTIL AP F e1 e2)) = true.
    intros c e1 e2.
    rewrite sat_val_until_eq.
    destruct (filter (until_is_achieved AP F sat_val c e1 e2) (until_candidates AP F f_to_f e1 e2)) as [| x xs] eqn:Hf.
    - exfalso. apply (sat_val_until_nonempty c e1 e2). exact Hf.
    - assert (
      In (fold_left unitinterval_max xs x) (filter (until_is_achieved AP F sat_val c e1 e2) (until_candidates AP F f_to_f e1 e2))) 
      as Hin. { 
        rewrite Hf. apply fold_left_max_in. 
      }
      apply filter_In in Hin. destruct Hin as [_ H]. exact H.
  Qed.

  Lemma until_achieved_shift : forall c e1 e2 i (v : UnitInterval),
    until_candidate_le_e2_at_i AP F sat_val (nth_tail AP c 1) v e2 i ->
    until_candidate_eq_e2_at_i_or_e1_before_i AP F sat_val (nth_tail AP c 1) v e2 i e1 ->
    until_candidate_le_all_e1_before_i AP F sat_val (nth_tail AP c 1) v e1 i ->
    until_is_achieved AP F sat_val c e1 e2 (unitinterval_min (sat_val c e1) v) = true.
  Proof.
    intros c e1 e2 i v H1 H2 H3.
    apply until_is_achieved_iff. exists (S i).
    assert (nth_tail AP c (S i) = nth_tail AP (nth_tail AP c 1) i) as Hshift. { 
      rewrite (nth_tail_add AP c 1 i). f_equal. 
    } simpl in *.
    repeat split.
    - rewrite Hshift. apply (Rle_trans _ (proj1_sig v) _). apply Rmin_r. apply H1.
    - destruct (unitinterval_min_case (sat_val c e1) v) as [Heq | Heq]; rewrite Heq.
      + right. exists O. split; [lia|]. rewrite nth_tail_0. reflexivity.
      + destruct H2 as [H2a | [j [Hj H2b]]].
        * left. rewrite Hshift. exact H2a.
        * right. exists (S j). split; [lia|].
          rewrite H2b, (nth_tail_add AP c 1 j). reflexivity.
    - intros j Hj. destruct j as [| j'].
      + rewrite nth_tail_0. apply Rmin_l.
      + apply (Rle_trans _ (proj1_sig v) _). apply Rmin_r.
        assert (nth_tail AP c (S j') = nth_tail AP (nth_tail AP c 1) j') as Hshift'. { 
          rewrite (nth_tail_add AP c 1 j'). f_equal. 
        }
        rewrite Hshift'.
        apply H3. lia.
  Qed.

  Lemma until_min_le_until : forall c e1 e2,
    proj1_sig (unitinterval_min (sat_val c e1) (sat_val (nth_tail AP c 1) (UNTIL AP F e1 e2))) <=
    proj1_sig (sat_val c (UNTIL AP F e1 e2)).
  Proof.
    intros c e1 e2.
    assert ((until_is_achieved AP F sat_val (nth_tail AP c 1) e1 e2 (sat_val (nth_tail AP c 1) (UNTIL AP F e1 e2))) = true) as Htemp by apply (sat_val_until_achieved  (nth_tail AP c 1) e1 e2) .
    apply (until_is_achieved_iff) in Htemp.
    destruct Htemp as [i' [H1 [H2 H3]]].
    assert (until_is_achieved AP F sat_val c e1 e2
      (unitinterval_min (sat_val c e1) (sat_val (nth_tail AP c 1) (UNTIL AP F e1 e2))) = true) as Hach . { 
        apply (until_achieved_shift c e1 e2 i'); assumption.
    }
    assert (In (unitinterval_min (sat_val c e1) (sat_val (nth_tail AP c 1) (UNTIL AP F e1 e2)))
      (until_candidates AP F f_to_f e1 e2)) as Hcand . { 
      unfold until_candidates.
      destruct (unitinterval_min_case (sat_val c e1) (sat_val (nth_tail AP c 1) (UNTIL AP F e1 e2))) as [Heq | Heq]; rewrite Heq.
      - apply in_or_app. left. apply proof2.
      - apply in_or_app.
        assert (Hin2 : In (sat_val (nth_tail AP c 1) (UNTIL AP F e1 e2))
          (possible_statsfaction_values (UNTIL AP F e1 e2))) by apply proof2.
        simpl in Hin2. apply in_app_or in Hin2. exact Hin2. 
    }
    assert (In (unitinterval_min (sat_val c e1) (sat_val (nth_tail AP c 1) (UNTIL AP F e1 e2)))
      (filter (until_is_achieved AP F sat_val c e1 e2) (until_candidates AP F f_to_f e1 e2))) as Hin_filter. { 
        apply filter_In. split; assumption. 
    }
    rewrite (sat_val_until_eq c e1 e2).
    destruct (filter (until_is_achieved AP F sat_val c e1 e2) (until_candidates AP F f_to_f e1 e2)) as [| x xs] eqn:Hf.
    - simpl in Hin_filter. contradiction.
    - apply fold_left_max_upper_bound. exact Hin_filter.
  Qed.

  Lemma until_achieved_bound : forall c e1 e2 i (value : R),
    value <= proj1_sig (sat_val (nth_tail AP c i) e2) ->
    (forall j, (j < i)%nat -> value <= proj1_sig (sat_val (nth_tail AP c j) e1)) ->
    value <= proj1_sig (sat_val c (UNTIL AP F e1 e2)).
  Proof.
    intros c e1 e2 i. revert c.
    induction i as [| i' IHi]; intros c value Hle Hbound.
    - rewrite nth_tail_0 in Hle. apply (Rle_trans _ (proj1_sig (sat_val c e2)) _ ). apply Hle.
      apply sat_val_e2_le_until.
    - assert (value <= proj1_sig (sat_val c e1)) as Hle1. { 
        rewrite <- (nth_tail_0 AP c). apply Hbound. lia. 
      }
      assert (value <= proj1_sig (sat_val (nth_tail AP c 1) (UNTIL AP F e1 e2))) as HleS. { 
        apply (IHi (nth_tail AP c 1)).
        - assert (nth_tail AP (nth_tail AP c 1) i' = nth_tail AP c (S i')) as Hshift. { 
            rewrite (nth_tail_add AP c 1 i'). f_equal. 
          } rewrite Hshift. exact Hle.
        - intros j Hj. assert (nth_tail AP (nth_tail AP c 1) j = nth_tail AP c (S j)) as Hshift. { 
            rewrite (nth_tail_add AP c 1 j). f_equal. 
          }
          rewrite Hshift. apply Hbound. lia. 
      }
      assert (proj1_sig (unitinterval_min (sat_val c e1) (sat_val (nth_tail AP c 1) (UNTIL AP F e1 e2))) <=
      proj1_sig (sat_val c (UNTIL AP F e1 e2))) as Huntil_min by apply until_min_le_until. 
      apply (Rle_trans _ (proj1_sig (unitinterval_min (sat_val c e1) (sat_val (nth_tail AP c 1) (UNTIL AP F e1 e2)))) _ ).
      unfold unitinterval_min. simpl. apply Rmin_glb; assumption. apply Huntil_min.
  Qed.

  Lemma achieved_le_max_step : forall c e1 e2 i (value : R),
    value <= proj1_sig (sat_val (nth_tail AP c i) e2) ->
    (forall j, (j < i)%nat -> value <= proj1_sig (sat_val (nth_tail AP c j) e1)) ->
    value <= Rmax (proj1_sig (sat_val c e2))
      (Rmin (proj1_sig (sat_val c e1)) (proj1_sig (sat_val (nth_tail AP c 1) (UNTIL AP F e1 e2)))).
  Proof.
    intros c e1 e2 i. revert c.
    induction i as [| i' _]; intros c value Hle Hbound.
    - rewrite nth_tail_0 in Hle. apply (Rle_trans _ (proj1_sig (sat_val c e2)) _). apply Hle. apply Rmax_l.
    - assert (value <= proj1_sig (sat_val c e1)) as Hle1. { 
        rewrite <- (nth_tail_0 AP c). apply Hbound. lia. 
      }
      assert (value <= proj1_sig (sat_val (nth_tail AP c 1) (UNTIL AP F e1 e2))) as HleS . { 
        apply (until_achieved_bound (nth_tail AP c 1) e1 e2 i').
        - assert (nth_tail AP (nth_tail AP c 1) i' = nth_tail AP c (S i')) as Hshift. { 
            rewrite (nth_tail_add AP c 1 i'). f_equal. 
          } rewrite Hshift. exact Hle.
        - intros j Hj. assert (nth_tail AP (nth_tail AP c 1) j = nth_tail AP c (S j)) as Hshift. { 
            rewrite (nth_tail_add AP c 1 j). f_equal. 
          } rewrite Hshift. apply Hbound. lia. 
      }
      apply (Rle_trans _ (Rmin (proj1_sig (sat_val c e1)) (proj1_sig (sat_val (nth_tail AP c 1) (UNTIL AP F e1 e2)))) _ ).
      apply Rmin_glb; assumption. apply Rmax_r.
  Qed.

  Lemma sat_val_until_step : forall c e1 e2,
    sat_val c (UNTIL AP F e1 e2) =
    unitinterval_max (sat_val c e2)
      (unitinterval_min (sat_val c e1) (sat_val (nth_tail AP c 1) (UNTIL AP F e1 e2))).
  Proof.
    intros c e1 e2. apply unitinterval_eq. apply Rle_antisym.
    - (* proj1_sig (sat_val c (UNTIL e1 e2)) <= proj1_sig (Rmax ...) *)
      assert (until_is_achieved AP F sat_val c e1 e2 (sat_val c (UNTIL AP F e1 e2)) = true) as Htemp
      by apply sat_val_until_achieved.
      apply until_is_achieved_iff in Htemp. destruct Htemp as [i [H1 [_ H3]]].
      apply (achieved_le_max_step c e1 e2 i); assumption.
    - (* proj1_sig (Rmax ...) <= proj1_sig (sat_val c (UNTIL e1 e2)) *)
      apply Rmax_lub.
      + apply sat_val_e2_le_until.
      + apply until_min_le_until.
  Qed.

  Definition countAbove (v0 : R) (vals : list R) : nat :=
    length (filter (fun v => if Rlt_dec v0 v then true else false) vals).

  Lemma filter_length_le : forall (A:Type) (P1 P2 : A -> bool) (l : list A),
    (forall x, P2 x = true -> P1 x = true) ->
    (length (filter P2 l) <= length (filter P1 l))%nat.
  Proof.
    intros A P1 P2 l Himp.
    induction l as [| x xs IH]; simpl.
    - lia.
    - destruct (P2 x) eqn:HP2.
      + apply Himp in HP2 as HP1. rewrite HP1. simpl. lia.
      + destruct (P1 x); simpl; lia.
  Qed.

  Lemma filter_length_lt : forall (A:Type) (P1 P2 : A -> bool) (l : list A) (x : A),
    (forall y, P2 y = true -> P1 y = true) ->
    In x l -> P1 x = true -> P2 x = false ->
    (length (filter P2 l) < length (filter P1 l))%nat.
  Proof.
    intros A P1 P2 l x Himp Hin HP1x HP2x.
    induction l as [| y ys IH]; simpl in *.
    - contradiction.
    - destruct Hin as [Heq | Hin].
      + subst y. rewrite HP1x, HP2x. simpl.
        pose proof (filter_length_le A P1 P2 ys Himp) as Hle. simpl. lia.
      + destruct (P2 y) eqn:HP2y.
        * apply Himp in HP2y as HP1y. rewrite HP1y. simpl. apply IH in Hin. lia.
        * destruct (P1 y) eqn:HP1y; simpl; apply IH in Hin; lia.
  Qed.

  Lemma countAbove_lt : forall v0 v1 vals,
    v0 < v1 -> In v1 vals -> (countAbove v1 vals < countAbove v0 vals)%nat.
  Proof.
    intros v0 v1 vals Hlt Hin.
    unfold countAbove.
    apply (filter_length_lt R
      (fun v => if Rlt_dec v0 v then true else false)
      (fun v => if Rlt_dec v1 v then true else false)
      vals v1).
    - intros y Hy. destruct (Rlt_dec v1 y) eqn:E; try discriminate.
      destruct (Rlt_dec v0 y) eqn:E'; [reflexivity|].
      exfalso. apply n. lra.
    - exact Hin.
    - destruct (Rlt_dec v0 v1); [reflexivity | exfalso; apply n; exact Hlt].
    - destruct (Rlt_dec v1 v1); [exfalso; lra | reflexivity].
  Qed.

  Lemma Rle_of_chain_mono : forall (f : nat -> R), (forall n, f n <= f (S n)) -> forall n, f 0%nat <= f n.
  Proof.
    intros f Hmono n. induction n as [| n IH].
    - apply Rle_refl.
    - eapply Rle_trans; [exact IH | apply Hmono].
  Qed.

  Lemma stabilizes_aux : forall k vals f,
    (forall n, In (f n) vals) ->
    (forall n, f n <= f (S n)) ->
    (countAbove (f 0%nat) vals <= k)%nat ->
    exists N, forall n, (N <= n)%nat -> f n = f N.
  Proof.
    induction k as [| k' IHk]; intros vals f Hin Hmono Hcnt.
    - exists 0%nat. intros n _.
      assert (Hge : f 0%nat <= f n) by (apply Rle_of_chain_mono; exact Hmono).
      assert (Hle : f n <= f 0%nat).
      { destruct (Rlt_dec (f 0%nat) (f n)) as [Hlt | Hnlt].
        - exfalso.
          assert (Habove : (countAbove (f 0%nat) vals <> 0)%nat).
          { unfold countAbove.
            assert (Hinl : In (f n) (filter (fun v => if Rlt_dec (f 0%nat) v then true else false) vals)).
            { apply filter_In. split; [apply Hin|]. destruct (Rlt_dec (f 0%nat) (f n)); [reflexivity | contradiction]. }
            destruct (filter (fun v => if Rlt_dec (f 0%nat) v then true else false) vals); [contradiction | simpl; lia]. }
          lia.
        - lra. }
      lra.
    - destruct (classic (forall n, f n = f 0%nat)) as [Hconst | Hnc].
      + exists 0%nat. intros n _. apply Hconst.
      + apply not_all_ex_not in Hnc as [n0 Hn0].
        assert (Hge0 : f 0%nat <= f n0) by (apply Rle_of_chain_mono; exact Hmono).
        assert (Hex : exists n, f 0%nat < f n).
        { exists n0. destruct Hge0 as [Hlt | Heq]; [exact Hlt | exfalso; apply Hn0; symmetry; exact Heq]. }
        destruct (dec_inh_nat_subset_has_unique_least_element (fun n => f 0%nat < f n))
          as [m [[Hpm Hleast] _]].
        * intros n. destruct (Rlt_dec (f 0%nat) (f n)); [left|right]; assumption.
        * exact Hex.
        * assert (Hcnt' : (countAbove (f m) vals <= k')%nat).
          { assert (Hlt2 : (countAbove (f m) vals < countAbove (f 0%nat) vals)%nat).
            { apply countAbove_lt; [exact Hpm | apply Hin]. }
            lia. }
          assert (Hin' : forall n, In (f (m + n)%nat) vals) by (intros n; apply Hin).
          assert (Hmono' : forall n, f (m + n)%nat <= f (m + S n)%nat).
          { intros n. replace (m + S n)%nat with (S (m + n))%nat by lia. apply Hmono. }
          assert (Hcnt'' : (countAbove (f (m + 0)%nat) vals <= k')%nat).
          { rewrite Nat.add_0_r. exact Hcnt'. }
          destruct (IHk vals (fun n => f (m + n)%nat) Hin' Hmono' Hcnt'') as [N' HN'].
          exists (m + N')%nat. intros n Hn.
          replace n with (m + (n - m))%nat by lia.
          assert (HNn : (N' <= n - m)%nat) by lia.
          specialize (HN' (n - m)%nat HNn). simpl in HN'. exact HN'.
  Qed.

Lemma stabilizes : forall vals f,
  (forall n, In (f n) vals) ->
  (forall n, f n <= f (S n)) ->
  exists N, forall n, (N <= n)%nat -> f n = f N.
Proof.
  intros vals f Hin Hmono.
  apply (stabilizes_aux (countAbove (f 0%nat) vals) vals f Hin Hmono).
  lia.
Qed.

Lemma eventually_resolves : forall c e1 e2,
  exists n, sat_val (nth_tail AP c n) (UNTIL AP F e1 e2) = sat_val (nth_tail AP c n) e2.
Proof.
  intros c e1 e2.
  destruct (classic (exists n, sat_val (nth_tail AP c n) (UNTIL AP F e1 e2) = sat_val (nth_tail AP c n) e2)) as [Hyes | Hno].
  - exact Hyes.
  - exfalso.
    assert (Hnever : forall n, sat_val (nth_tail AP c n) (UNTIL AP F e1 e2) <> sat_val (nth_tail AP c n) e2).
    { intros n Heq. apply Hno. exists n. exact Heq. }
    set (f := fun n => proj1_sig (sat_val (nth_tail AP c n) (UNTIL AP F e1 e2))).
    set (vals := ListDef.map (fun v => proj1_sig v) (possible_statsfaction_values (UNTIL AP F e1 e2))).
    assert (Hin_f : forall n, In (f n) vals).
    { intro n. unfold f, vals. apply in_map. apply proof2. }
    assert (Hstrict : forall n,
      proj1_sig (sat_val (nth_tail AP c n) e2) < proj1_sig (sat_val (nth_tail AP c n) (UNTIL AP F e1 e2))).
    { intro n.
      assert (Hle : proj1_sig (sat_val (nth_tail AP c n) e2) <= proj1_sig (sat_val (nth_tail AP c n) (UNTIL AP F e1 e2)))
        by apply sat_val_e2_le_until.
      destruct Hle as [Hlt' | Heq']; [exact Hlt' | exfalso; apply (Hnever n); apply unitinterval_eq; symmetry; exact Heq']. }
    assert (Hmono : forall n, f n <= f (S n)).
    { intro n. unfold f.
      assert (Hshift : nth_tail AP (nth_tail AP c n) 1 = nth_tail AP c (S n)).
      { rewrite (nth_tail_add AP c n 1). f_equal. lia. }
      assert (Heqn : proj1_sig (sat_val (nth_tail AP c n) (UNTIL AP F e1 e2)) =
        Rmax (proj1_sig (sat_val (nth_tail AP c n) e2))
             (Rmin (proj1_sig (sat_val (nth_tail AP c n) e1)) (proj1_sig (sat_val (nth_tail AP c (S n)) (UNTIL AP F e1 e2))))).
      { rewrite (sat_val_until_step (nth_tail AP c n) e1 e2).
        unfold unitinterval_max, unitinterval_min. simpl. rewrite Hshift. reflexivity. }
      rewrite Heqn.
      destruct (Rle_dec (proj1_sig (sat_val (nth_tail AP c n) e2))
                (Rmin (proj1_sig (sat_val (nth_tail AP c n) e1)) (proj1_sig (sat_val (nth_tail AP c (S n)) (UNTIL AP F e1 e2)))))
        as [Hle | Hgt].
      - rewrite (Rmax_right _ _ Hle). apply Rmin_r.
      - exfalso. apply Rnot_le_lt in Hgt.
        pose proof (Hstrict n) as Hs. rewrite Heqn in Hs.
        rewrite (Rmax_left _ _ (Rlt_le _ _ Hgt)) in Hs.
        lra. }
    destruct (stabilizes vals f Hin_f Hmono) as [N HN].
    assert (Hach : until_is_achieved AP F sat_val (nth_tail AP c N) e1 e2 (sat_val (nth_tail AP c N) (UNTIL AP F e1 e2)) = true)
      by apply sat_val_until_achieved.
    destruct (proj1 (until_is_achieved_iff sat_val (nth_tail AP c N) e1 e2 (sat_val (nth_tail AP c N) (UNTIL AP F e1 e2))) Hach)
      as [i [H1 [H2 H3]]].
    assert (Hshift2 : nth_tail AP (nth_tail AP c N) i = nth_tail AP c (N + i)%nat).
    { rewrite (nth_tail_add AP c N i). reflexivity. }
    simpl in *. rewrite Hshift2 in H1.
    assert (HfNi : f (N + i)%nat = f N) by (apply HN; lia).
    unfold f in HfNi.
    pose proof (Hstrict (N + i)%nat) as Hlt2.
    lra.
Qed.

End until_lemmas.

