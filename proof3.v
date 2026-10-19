From LTL_F_Project Require Import ltl_f.
From LTL_F_Project Require Import ngbw.
From LTL_F_Project Require Import utils.
From LTL_F_Project Require Import proof2.
From LTL_F_Project Require Import until_lemmas.
From LTL_F_Project Require Import nbgw_for_ltl_f.
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

Section lemma3a.
  (* Nbgw accepts -> ltl-f satisfies *)

  Variables AP F : Set.
  Variable f_to_f : F -> (list UnitInterval -> UnitInterval).

  Variable expression : ltl_f_expr AP F.
  Variable predicate : list UnitInterval.

  Let isSubExpr := isSubExpr AP F.
  Let isSubExpr_refl := isSubExpr_refl AP F.
  Let isSubExpr_trans := isSubExpr_trans AP F.
  Let isSubExpr_next_child := isSubExpr_next_child AP F.
  Let isSubExpr_until_child1 := isSubExpr_until_child1 AP F.
  Let isSubExpr_until_child2 := isSubExpr_until_child2 AP F.
  Let isSubExpr_FTerm_child := isSubExpr_FTerm_child AP F.

  Let consistent (state : ltl_f_expr AP F -> UnitInterval) :=
    (forall e, isSubExpr expression e ->
    (e = TRUE AP F -> state (e) = one) /\
    (e = FALSE AP F -> state (e) = zero) /\
    (forall p, e = AP_TERM AP F p -> (state (e) = zero \/ state (e) = one)) /\
    (forall f l, e = F_TERM AP F f l -> (state (e) = ((f_to_f f) (ListDef.map state l)))))
  .

  Let Alphabet := (AP -> AtomicProposition).
  Let State := {g : ltl_f_expr AP F -> UnitInterval | consistent g}.

  Let TransistionFunction (letter : Alphabet) (from : State) :=
    fun (to : State) => forall e, isSubExpr expression e -> (
    (forall ap, e = AP_TERM AP F ap -> ((letter ap = AP1 -> (proj1_sig from) e = one) /\ (letter ap = AP0 -> (proj1_sig from) e = zero))) /\
    (forall e1, e = (NEXT AP F e1) -> ((proj1_sig from) e = (proj1_sig to) (e1))) /\
    (forall e1 e2, e = (UNTIL AP F e1 e2) -> ((proj1_sig from) (UNTIL AP F e1 e2)) =
      unitinterval_max ((proj1_sig from) e2) (unitinterval_min ((proj1_sig from) e1) ((proj1_sig to) (UNTIL AP F e1 e2))))).

  Let IntialState (state: State) :=
    In ((proj1_sig state) expression) predicate.

  Let FinalState (e1 e2 : ltl_f_expr AP F) :=
    fun (state : State) => (proj1_sig state) (e2) = (proj1_sig state) (UNTIL AP F e1 e2).

  Let FinalStates (finalSet : State -> Prop) :=
    exists e1 e2, isSubExpr expression (UNTIL AP F e1 e2) /\ (FinalState e1 e2) = finalSet.

  Let sat_val := sat_val AP F f_to_f.
  Let satisfied_by_on := satisfied_by_on Alphabet State TransistionFunction IntialState FinalStates.

  Variable word : Stream Alphabet.
  Variable run : Stream State.
  Let computation := (INFINITE AP word).
  Let g (i : nat) (expr : ltl_f_expr AP F) := ((proj1_sig (Str_nth i run)) expr).

  Lemma nth_tail_add : forall (a b : nat),
    nth_tail AP (nth_tail AP computation a) b = nth_tail AP computation (a + b).
  Proof.
    intros a b. unfold computation. simpl. f_equal. rewrite Str_nth_tl_plus. f_equal. lia.
  Qed.

  Section until_step.
    Variables e1 e2 : ltl_f_expr AP F.

    Local Notation "a <== b" := (proj1_sig a <= proj1_sig b) (at level 70, no associativity).

    Hypothesis Hstep : forall n,
      g n (UNTIL AP F e1 e2) =
      unitinterval_max (g n e2) (unitinterval_min (g n e1) (g (S n) (UNTIL AP F e1 e2))).

    Lemma until_unroll : forall (o i : nat),
      g (i + o) (UNTIL AP F e1 e2) = g (i + o) e2 ->
      exists w, (w <= o)%nat /\
        g i (UNTIL AP F e1 e2) <== g (i + w) e2 /\
        (g i (UNTIL AP F e1 e2) = g (i + w) e2 \/
         exists j, (j < w)%nat /\ g i (UNTIL AP F e1 e2) = g (i + j) e1) /\
        (forall j, (j < w)%nat -> g i (UNTIL AP F e1 e2) <== g (i + j) e1).
    Proof.
      induction o as [| o' IH]; intros i Hbase.
      - exists 0%nat. rewrite Nat.add_0_r in *.
        repeat split.
        + lia.
        + rewrite Hbase. apply Rle_refl.
        + left. exact Hbase.
        + intros j Hj. lia.
      - assert ( g (S i + o') (UNTIL AP F e1 e2) = g (S i + o') e2) as Hbase'. { 
          rewrite Nat.add_succ_comm. exact Hbase. 
        }
        destruct (IH (S i) Hbase') as [w' [Hw'o [Hb2 [Htight Hb1]]]].
        destruct (Rle_dec (proj1_sig (g i e2))
                          (proj1_sig (unitinterval_min (g i e1) (g (S i) (UNTIL AP F e1 e2)))))
          as [Hle | Hgt].
        + (* e2 here is dominated by the min: the witness moves one step further out *)
          exists (S w').
          assert (g i (UNTIL AP F e1 e2) = unitinterval_min (g i e1) (g (S i) (UNTIL AP F e1 e2))) as Hgi. { 
            rewrite (Hstep i). apply ui_max_is_r. exact Hle. 
          }
          repeat split.
          * lia.
          * rewrite Hgi, <- Nat.add_succ_comm. apply (Rle_trans _ (proj1_sig (g (S i) (UNTIL AP F e1 e2))) _).
            apply ui_min_r.  apply Hb2.
          * destruct (Rle_dec (proj1_sig (g i e1)) (proj1_sig (g (S i) (UNTIL AP F e1 e2))))
              as [Hle1 | Hgt1].
            -- (* e1 here is the smaller one, so it is itself the tight witness *)
               right. exists 0%nat. split. lia. rewrite Hgi, Nat.add_0_r. 
               apply ui_min_is_l. exact Hle1.
            -- (* the tail value carries: inherit the IH's tight witness, shifted *)
               assert (g i (UNTIL AP F e1 e2) = g (S i) (UNTIL AP F e1 e2)) as Hgi'. { 
                 rewrite Hgi. apply ui_min_is_r. lra.
               }
               rewrite Hgi'.
               destruct Htight as [Ht2 | [j [Hj Ht1]]].
               ++ left. rewrite <- Nat.add_succ_comm. exact Ht2.
               ++ right. exists (S j). split. lia.
                  rewrite <- Nat.add_succ_comm. exact Ht1.
          * intros j Hj. destruct j as [| j'].
            -- rewrite Hgi, Nat.add_0_r. apply ui_min_l.
            -- rewrite Hgi, <- Nat.add_succ_comm. apply (Rle_trans _ (proj1_sig (g (S i) (UNTIL AP F e1 e2))) _).
               apply ui_min_r. apply Hb1. lia.
        + (* e2 here already dominates: the witness is right here, at offset 0 *)
          exists 0%nat.
          assert (g i (UNTIL AP F e1 e2) = g i e2) as Hgi. { 
            rewrite (Hstep i). apply ui_max_is_l. lra. 
          }
          rewrite Nat.add_0_r.
          repeat split.
          * lia.
          * rewrite Hgi. apply Rle_refl.
          * left. exact Hgi.
          * intros j Hj. lia.
    Qed.

    (* If [value] is dominated by e2 at offset o and by every e1-value strictly before o
       (i.e. [value] is an until_is_achieved-style candidate at witness o, phrased directly
       in terms of g), then [value] is dominated by g's own UNTIL value at the start
       position. This is what makes g's value the actual maximum over all witnesses, not
       just a witness itself. *)
    Lemma until_dominates : forall (o i : nat) (value : UnitInterval),
      value <== g (i + o) e2 ->
      (forall j, (j < o)%nat -> value <== g (i + j) e1) ->
      value <== g i (UNTIL AP F e1 e2).
    Proof.
      induction o as [| o' IH]; intros i value Hle Hbound.
      - rewrite Nat.add_0_r in Hle.
        rewrite (Hstep i). eapply Rle_trans; [exact Hle | apply ui_max_l].
      - assert (Hle1 : value <== g i e1).
        { specialize (Hbound 0%nat). rewrite Nat.add_0_r in Hbound. apply Hbound. lia. }
        assert (HleS : value <== g (S i) (UNTIL AP F e1 e2)).
        { apply (IH (S i)).
          - rewrite Nat.add_succ_comm. exact Hle.
          - intros j Hj. rewrite Nat.add_succ_comm. apply Hbound. lia. }
        rewrite (Hstep i).
        eapply Rle_trans; [| apply ui_max_r].
        apply Rmin_glb; assumption.
    Qed.
  End until_step.

  Lemma nbgwAcceptingRunsSatisfiesLtlFAtEveryI: forall expr, isSubExpr expression expr ->
    satisfied_by_on word run -> forall i, 
    sat_val (nth_tail AP computation i) expr = (g i expr).
  intros expr.
  induction expr as [ | | ap | l f IH | e IH | e1 e2 IH] using ltl_f_induction_principle.
    - intros Hsub Hngbw i. assert (g i (TRUE AP F) = one) as Htrue. {
      unfold g in *. destruct (Str_nth i run). simpl. specialize (c (TRUE AP F)). apply c in Hsub as c1.
      destruct c1 as [Htrue Hrest]. auto.
    } rewrite Htrue. reflexivity.
    - intros Hsub Hngbw i. assert (g i (FALSE AP F) = zero) as Hfalse. {
       unfold g in *. destruct (Str_nth i run). simpl. specialize (c (FALSE AP F)). apply c in Hsub as c1.
      destruct c1 as [Htrue [Hflase Hrest]]. auto.
    } rewrite Hfalse. constructor.
    - intros Hsub Hngbw i. 
      unfold satisfied_by_on in Hngbw ; unfold ngbw.satisfied_by_on in Hngbw. 
      destruct Hngbw as [[Hintial Hreach] Hfinal].
      unfold allStatesReachble in Hreach. 
      unfold TransistionFunction in Hreach. specialize (Hreach i (AP_TERM AP F ap)). 
      apply Hreach in Hsub as Hreach'. destruct Hreach' as [Htap [Hnext Huntil]].
      specialize (Htap ap). destruct Htap as [Hap1 Hap0]. reflexivity. unfold g. 
      simpl. assert ((Str_nth i word) ap = AP0 \/ (Str_nth i word) ap = AP1) as Hap 
      by apply atomic_proposition_one_or_zero. destruct Hap as [Hap | Hap].
      + apply Hap0 in Hap as Hg. rewrite Hg. unfold Str_nth in Hap.
        unfold Str_nth. simpl. unfold Alphabet in Hap. (* I am going to punch a french person*) rewrite Hap.
        simpl. apply f_equal. apply proof_irrelevance.
      + apply Hap1 in Hap as Hg. rewrite Hg. unfold Str_nth in Hap.
        unfold Str_nth. simpl. unfold Alphabet in Hap. rewrite Hap. simpl.
        apply f_equal. apply proof_irrelevance.
    - intros Hsub Hngbw i. assert (g i (F_TERM AP F f l) = ((f_to_f f) (ListDef.map (g i) l))) as Hf. {
        unfold g in *. destruct (Str_nth i run). simpl. specialize (c (F_TERM AP F f l)). apply c in Hsub as c1.
        destruct c1 as [Htrue [Hfalse [Hap Hf]]]. auto.
      } rewrite Hf. simpl. f_equal. apply map_ext_in. intros x Hin.
      apply IH ; try assumption. apply (isSubExpr_trans expression (F_TERM AP F f l)  x ).
      apply Hsub. apply isSubExpr_FTerm_child. apply Hin.
    - intros Hsub Hngbw i. pose proof Hngbw as Hngbw'.
      destruct Hngbw as [[Hintial Hreach] Hfinal].
      unfold allStatesReachble in Hreach. unfold TransistionFunction in Hreach. 
      specialize (Hreach i (NEXT AP F e)). apply Hreach in Hsub as Hreach'.
      destruct Hreach' as [Hap [Hnext Huntil]]. clear Huntil Hap Hfinal.
      assert (Hspec : sat_val (nth_tail AP computation i) (NEXT AP F e) =
        sat_val (nth_tail AP (nth_tail AP computation i) 1) e) by reflexivity.
      rewrite Hspec, (nth_tail_add i 1).
      assert (isSubExpr expression e) as Hsube. {
        apply (isSubExpr_trans expression (NEXT AP F e) e). apply Hsub. apply isSubExpr_next_child.
      }
      rewrite (IH Hsube Hngbw' (i + 1)%nat).
      unfold g. assert (NEXT AP F e = NEXT AP F e) as Href by reflexivity. rewrite (Hnext e Href). reflexivity.
    - intros Hsub Hngbw i. destruct IH as [IHe1 IHe2]. pose proof Hngbw as Hngbw'.
      destruct Hngbw as [[Hintial Hreach] Hfinal].
      assert (FinalStates (FinalState e1 e2)) as Hfinal'. {
        unfold FinalStates. exists e1. exists e2. split; [exact Hsub | reflexivity].
      }
      destruct (Hfinal (FinalState e1 e2) Hfinal' i) as [k0 [Hik0 Hk0]].
      remember (k0 - i)%nat as k eqn:Hkeq.
      assert (Hik0' : (i + k)%nat = k0) by lia.
      assert (Hbase_pos : g (i + k) (UNTIL AP F e1 e2) = g (i + k) e2).
      { unfold g at 1 2. rewrite Hik0'. symmetry. exact Hk0. }
      (* The transition function already states this at the UnitInterval level, so it
         transfers across verbatim -- no projecting down to Rmax/Rmin needed. *)
      assert (Hstep_all : forall n, g n (UNTIL AP F e1 e2) =
        unitinterval_max (g n e2) (unitinterval_min (g n e1) (g (S n) (UNTIL AP F e1 e2)))).
      { intros n.
        pose proof (Hreach n) as Hr. unfold TransistionFunction in Hr.
        specialize (Hr (UNTIL AP F e1 e2)). apply Hr in Hsub as Hr'.
        destruct Hr' as [Htap [Hnextc Huntilc]].
        specialize (Huntilc e1 e2 eq_refl).
        replace (n + 1)%nat with (S n) in Huntilc by lia.
        exact Huntilc. }
      destruct (until_unroll e1 e2 Hstep_all k i Hbase_pos) as [w [Hwk [H3w [H4w H6w]]]].
      assert (Hsube1 : isSubExpr expression e1).
      { apply (isSubExpr_trans expression (UNTIL AP F e1 e2) e1). exact Hsub. apply isSubExpr_until_child1. }
      assert (Hsube2 : isSubExpr expression e2).
      { apply (isSubExpr_trans expression (UNTIL AP F e1 e2) e2). exact Hsub. apply isSubExpr_until_child2. }
      assert (Ee1 : forall j, sat_val (nth_tail AP computation j) e1 = g j e1) by (apply IHe1; assumption).
      assert (Ee2 : forall j, sat_val (nth_tail AP computation j) e2 = g j e2) by (apply IHe2; assumption).
      assert (Hspec : sat_val (nth_tail AP computation i) (UNTIL AP F e1 e2) =
        match filter (until_is_achieved AP F sat_val (nth_tail AP computation i) e1 e2)
                     (until_candidates AP F f_to_f e1 e2) with
        | [] => zero
        | x :: xs => fold_left unitinterval_max xs x
        end) by reflexivity.
      (* g i (UNTIL e1 e2) is itself achieved, at witness w (translated from until_unroll
         through IHe1/IHe2/nth_tail_add), and lies in the candidate list via proof2. *)
      assert (HachG : until_is_achieved AP F sat_val (nth_tail AP computation i) e1 e2 (g i (UNTIL AP F e1 e2)) = true).
      { apply until_is_achieved_iff. exists w.
        unfold until_candidate_le_e2_at_i, until_candidate_eq_e2_at_i_or_e1_before_i,
               until_candidate_le_all_e1_before_i.
        rewrite (nth_tail_add i w). rewrite Ee2. split; [exact H3w|]. split.
        - destruct H4w as [Heq2 | [j [Hjw Heq1]]].
          + left. exact Heq2.
          + right. exists j. split; [exact Hjw|].
            rewrite (nth_tail_add i j). rewrite Ee1. exact Heq1.
        - intros j Hjw. rewrite (nth_tail_add i j). rewrite Ee1. apply H6w. exact Hjw. }
      assert (Hin_cand : In (g i (UNTIL AP F e1 e2)) (until_candidates AP F f_to_f e1 e2)).
      { unfold until_candidates. destruct H4w as [Heq2 | [j [Hjw Heq1]]].
        - apply in_or_app. right.
          assert (Heq : g i (UNTIL AP F e1 e2) = sat_val (nth_tail AP computation (i + w)) e2).
          { rewrite Ee2. exact Heq2. }
          rewrite Heq. apply proof2.
        - apply in_or_app. left.
          assert (Heq : g i (UNTIL AP F e1 e2) = sat_val (nth_tail AP computation (i + j)) e1).
          { rewrite Ee1. exact Heq1. }
          rewrite Heq. apply proof2. }
      assert (Hin_filter : In (g i (UNTIL AP F e1 e2))
        (filter (until_is_achieved AP F sat_val (nth_tail AP computation i) e1 e2) (until_candidates AP F f_to_f e1 e2))).
      { apply filter_In. split; assumption. }
      rewrite Hspec.
      destruct (filter (until_is_achieved AP F sat_val (nth_tail AP computation i) e1 e2) (until_candidates AP F f_to_f e1 e2))
        as [| x xs] eqn:Hf.
      + simpl in Hin_filter. contradiction.
      + apply unitinterval_eq. apply Rle_antisym.
        * (* proj1_sig (fold_left unitinterval_max xs x) <= proj1_sig (g i (UNTIL e1 e2)) *)
          assert (Hin_LHS : In (fold_left unitinterval_max xs x)
            (filter (until_is_achieved AP F sat_val (nth_tail AP computation i) e1 e2) (until_candidates AP F f_to_f e1 e2))).
          { rewrite Hf. apply fold_left_max_in. }
          apply filter_In in Hin_LHS. destruct Hin_LHS as [_ HachLHS].
          destruct (proj1 (until_is_achieved_iff AP F sat_val (nth_tail AP computation i) e1 e2
                              (fold_left unitinterval_max xs x)) HachLHS) as [i' [Hle [_ Hbound]]].
          unfold until_candidate_le_e2_at_i in Hle.
          unfold until_candidate_le_all_e1_before_i in Hbound.
          apply (until_dominates e1 e2 Hstep_all i' i).
          -- rewrite (nth_tail_add i i') in Hle. rewrite Ee2 in Hle. exact Hle.
          -- intros j Hj. specialize (Hbound j Hj). rewrite (nth_tail_add i j) in Hbound. rewrite Ee1 in Hbound. exact Hbound.
        * (* proj1_sig (g i (UNTIL e1 e2)) <= proj1_sig (fold_left unitinterval_max xs x) *)
          apply fold_left_max_upper_bound. exact Hin_filter.
  Qed.

End lemma3a.


Section lemma3b.
  (* ltl-f satisfies -> nbgw accepts *)

  Variables AP F : Set.
  Variable f_to_f : F -> (list UnitInterval -> UnitInterval).

  Variable expression : ltl_f_expr AP F.
  Variable predicate : list UnitInterval.

  Let isSubExpr := isSubExpr AP F.
  Let isSubExpr_refl := isSubExpr_refl AP F.
  Let isSubExpr_trans := isSubExpr_trans AP F.
  Let isSubExpr_next_child := isSubExpr_next_child AP F.
  Let isSubExpr_until_child1 := isSubExpr_until_child1 AP F.
  Let isSubExpr_until_child2 := isSubExpr_until_child2 AP F.
  Let isSubExpr_FTerm_child := isSubExpr_FTerm_child AP F.

  Let consistent (state : ltl_f_expr AP F -> UnitInterval) :=
    (forall e, isSubExpr expression e ->
    (e = TRUE AP F -> state (e) = one) /\
    (e = FALSE AP F -> state (e) = zero) /\
    (forall p, e = AP_TERM AP F p -> (state (e) = zero \/ state (e) = one)) /\
    (forall f l, e = F_TERM AP F f l -> (state (e) = ((f_to_f f) (ListDef.map state l)))))
  .

  Let Alphabet := (AP -> AtomicProposition).
  Let State := {g : ltl_f_expr AP F -> UnitInterval | consistent g}.

  Let TransistionFunction (letter : Alphabet) (from : State) :=
    fun (to : State) => forall e, isSubExpr expression e -> (
    (forall ap, e = AP_TERM AP F ap -> ((letter ap = AP1 -> (proj1_sig from) e = one) /\ (letter ap = AP0 -> (proj1_sig from) e = zero))) /\
    (forall e1, e = (NEXT AP F e1) -> ((proj1_sig from) e = (proj1_sig to) (e1))) /\
    (forall e1 e2, e = (UNTIL AP F e1 e2) -> ((proj1_sig from) (UNTIL AP F e1 e2)) =
      unitinterval_max ((proj1_sig from) e2) (unitinterval_min ((proj1_sig from) e1) ((proj1_sig to) (UNTIL AP F e1 e2))))).

  Let IntialState (state: State) :=
    In ((proj1_sig state) expression) predicate.

  Let FinalState (e1 e2 : ltl_f_expr AP F) :=
    fun (state : State) => (proj1_sig state) (e2) = (proj1_sig state) (UNTIL AP F e1 e2).

  Let FinalStates (finalSet : State -> Prop) :=
    exists e1 e2, isSubExpr expression (UNTIL AP F e1 e2) /\ (FinalState e1 e2) = finalSet.

  Let sat_val := sat_val AP F f_to_f.
  Let satisfied_by_on := satisfied_by_on Alphabet State TransistionFunction IntialState FinalStates.

  Variable word1 : Stream Alphabet.
  Variable run1 : Stream (ltl_f_expr AP F -> UnitInterval).
  Let computation1 := (INFINITE AP word1).

  Hypothesis run1_correspond_to_ltl_f : forall expr, isSubExpr expression expr ->
    (forall i, (Str_nth i run1) expr = sat_val (nth_tail AP computation1 i) expr).

  Lemma allStatesInRun1Consistent : forall s, (exists k, (Str_nth k run1) = s) -> consistent s.
    intros s [k Hk] e Hsub. repeat split.
    + intros He. subst e.
      specialize (run1_correspond_to_ltl_f (TRUE AP F) Hsub k) as Hcond.
      rewrite Hk in Hcond. rewrite Hcond. reflexivity.
    + intros He. subst e.
      specialize (run1_correspond_to_ltl_f (FALSE AP F) Hsub k) as Hcond.
      rewrite Hk in Hcond. rewrite Hcond. reflexivity.
    + intros p He. subst e.
      specialize (run1_correspond_to_ltl_f (AP_TERM AP F p) Hsub k) as Hcond.
      rewrite Hk in Hcond. rewrite Hcond.
      pose proof (proof2 AP F f_to_f (AP_TERM AP F p) (nth_tail AP computation1 k)) as Hp.
      simpl in Hp. destruct Hp as [Hp | [Hp | []]].
      * right. symmetry. exact Hp.
      * left. symmetry. exact Hp.
    + intros f l He. subst e.
      specialize (run1_correspond_to_ltl_f (F_TERM AP F f l) Hsub k) as Hcond.
      rewrite Hk in Hcond. rewrite Hcond. simpl. f_equal.
      apply map_ext_in. intros x Hin.
      assert (Hsubx : isSubExpr expression x). { 
        apply (isSubExpr_trans expression (F_TERM AP F f l) x). apply Hsub. apply isSubExpr_FTerm_child. apply Hin. 
      }
      specialize (run1_correspond_to_ltl_f x Hsubx k) as Hcondx.
      rewrite Hk in Hcondx.
      symmetry. assumption.
  Qed.

  Lemma bridge : forall n, consistent (Str_nth n run1).
   intros n. apply allStatesInRun1Consistent. exists n. reflexivity.
  Qed.

  Definition stateFromRun1 (n : nat) : State := exist _ (Str_nth n run1) (bridge n).

  Lemma allStatesInRun1CanTransitionToNextState : forall i, 
    TransistionFunction (Str_nth i word1) (stateFromRun1 i) (stateFromRun1 (i + 1)%nat).
    intros i. intros e Hsub. repeat split.
    + intros Hap. subst. simpl. specialize (run1_correspond_to_ltl_f (AP_TERM AP F ap) Hsub i) as Hcond.
      simpl in Hcond. rewrite Hcond. unfold Alphabet in *. rewrite (Str_nth_plus 0 i word1). simpl. 
      rewrite Hap. simpl. apply f_equal. apply proof_irrelevance.
    + intros Hap. subst. simpl. specialize (run1_correspond_to_ltl_f (AP_TERM AP F ap) Hsub i) as Hcond.
      simpl in Hcond. rewrite Hcond. unfold Alphabet in *. rewrite (Str_nth_plus 0 i word1). simpl. 
      rewrite Hap. simpl. apply f_equal. apply proof_irrelevance.
    + intros e1 He1. subst. simpl. assert (isSubExpr expression e1) as Hsube1. {
        apply (isSubExpr_trans expression (NEXT AP F e1) e1). apply Hsub. apply isSubExpr_next_child.
      }
      specialize (run1_correspond_to_ltl_f (NEXT AP F e1) Hsub i) as HcondNext.
      specialize (run1_correspond_to_ltl_f (e1) Hsube1 (i + 1)%nat) as Hconde1.
      rewrite HcondNext. rewrite Hconde1. simpl.  f_equal. f_equal.
      change (tl (Str_nth_tl i word1)) with (Str_nth_tl 1 (Str_nth_tl i word1)).
      rewrite Str_nth_tl_plus. f_equal. lia.
    + intros e1 e2 Heq. subst e. simpl.
      assert (Hsube1 : isSubExpr expression e1).
      { apply (isSubExpr_trans expression (UNTIL AP F e1 e2) e1). apply Hsub. apply isSubExpr_until_child1. }
      assert (Hsube2 : isSubExpr expression e2).
      { apply (isSubExpr_trans expression (UNTIL AP F e1 e2) e2). apply Hsub. apply isSubExpr_until_child2. }
      specialize (run1_correspond_to_ltl_f (UNTIL AP F e1 e2) Hsub i) as HcondU.
      specialize (run1_correspond_to_ltl_f e1 Hsube1 i) as Hconde1.
      specialize (run1_correspond_to_ltl_f e2 Hsube2 i) as Hconde2.
      specialize (run1_correspond_to_ltl_f (UNTIL AP F e1 e2) Hsub (i + 1)%nat) as HcondU'.
      rewrite HcondU, Hconde1, Hconde2, HcondU'.
      unfold sat_val.
      rewrite (sat_val_until_step AP F f_to_f (nth_tail AP computation1 i) e1 e2).
      rewrite (ltl_f.nth_tail_add AP computation1 i 1).
      reflexivity.
  Qed.


  (* [run] is the *unrelated* Stream State from the forward direction (Section variable
     declared long before word1/run1). The state stream that actually corresponds to run1
     is built here. *)
  CoFixpoint run1AsStates_from (n : nat) : Stream State :=
    Cons (stateFromRun1 n) (run1AsStates_from (S n)).
  Definition run1AsStates : Stream State := run1AsStates_from 0%nat.

  Lemma Str_nth_tl_run1AsStates_from : forall m n,
    Str_nth_tl m (run1AsStates_from n) = run1AsStates_from (m + n)%nat.
  Proof.
    intros m. induction m as [| m IH]; intro n.
    - reflexivity.
    - simpl. replace (S (m + n))%nat with (m + S n)%nat by lia. apply IH.
  Qed.

  Lemma Str_nth_run1AsStates : forall n, Str_nth n run1AsStates = stateFromRun1 n.
  Proof.
    intro n. unfold run1AsStates, Str_nth. rewrite Str_nth_tl_run1AsStates_from.
    rewrite Nat.add_0_r. reflexivity.
  Qed.

  Lemma if_satval_in_predicate_then_head_in_intial : 
    In (sat_val computation1 expression) predicate -> IntialState (hd run1AsStates).
    intros Hin. simpl. unfold IntialState. simpl.
    specialize (run1_correspond_to_ltl_f (expression) (isSubExpr_refl expression) 0)  as Hcond.
    rewrite Hcond. simpl. unfold computation1 in Hin. assumption.
  Qed.

  Lemma all_states_reachable_run1 : allStatesReachble Alphabet State TransistionFunction run1AsStates word1.
    unfold allStatesReachble. intros i. rewrite Str_nth_run1AsStates .  rewrite Str_nth_run1AsStates .
    apply allStatesInRun1CanTransitionToNextState.  
  Qed.

  (* Every UNTIL subformula's "final" condition (state e2 = state (UNTIL e1 e2)) holds at
     unboundedly many positions along run1AsStates: past any starting point k, eventually_resolves
     (a general, unconditional fact about sat_val proved above in Section proof2 via a finite-value
     stabilization argument) gives a resolution position, translated here via run1_correspond_to_ltl_f. *)
  Lemma run1_resolves_from : forall e1 e2 k, isSubExpr expression (UNTIL AP F e1 e2) ->
    exists n, FinalState e1 e2 (stateFromRun1 (k + n)%nat).
  Proof.
    intros e1 e2 k Hsub.
    destruct (eventually_resolves AP F f_to_f (nth_tail AP computation1 k) e1 e2) as [n Hn].
    exists n.
    assert (Hsube2 : isSubExpr expression e2).
    { apply (isSubExpr_trans expression (UNTIL AP F e1 e2) e2). exact Hsub. apply isSubExpr_until_child2. }
    specialize (run1_correspond_to_ltl_f (UNTIL AP F e1 e2) Hsub (k + n)%nat) as HcondU.
    specialize (run1_correspond_to_ltl_f e2 Hsube2 (k + n)%nat) as Hconde2.
    unfold FinalState, stateFromRun1. simpl.
    rewrite HcondU, Hconde2.
    rewrite (ltl_f.nth_tail_add AP computation1 k n) in Hn.
    symmetry. exact Hn.
  Qed.

  (* This is the standard Büchi-style "visits the final set infinitely often" fact, and it IS
     fully proved, unconditionally, from run1_correspond_to_ltl_f: *)
  Lemma run1VisitsFinalSetInfinitelyOften : forall e1 e2, isSubExpr expression (UNTIL AP F e1 e2) ->
    forall k, exists m, (k <= m)%nat /\ FinalState e1 e2 (stateFromRun1 m).
  Proof.
    intros e1 e2 Hsub k.
    destruct (run1_resolves_from e1 e2 k Hsub) as [n Hn].
    exists (k + n)%nat. split; [lia | exact Hn].
  Qed.

  (* NGBW acceptance is now stated at the set level (satisfied_by_on's Hfinal clause:
     forall set, FinalStates set -> forall i, exists k, i <= k /\ set (Str_nth k run)),
     not via InfinitelyOften/Eventually, so this is exactly run1VisitsFinalSetInfinitelyOften
     generalized from FinalState e1 e2 to an arbitrary FinalStates-classified set, via
     FinalStates's own witnesses. *)
  Lemma run1VistsAllStatesInFinalStatesInfinitelyOften : forall finalSet : State -> Prop,
    FinalStates finalSet -> forall i, exists k, (i <= k)%nat /\ finalSet (Str_nth k run1AsStates).
  Proof.
    intros finalSet [e1 [e2 [Hsub Heq]]] i.
    subst finalSet.
    destruct (run1VisitsFinalSetInfinitelyOften e1 e2 Hsub i) as [m [Him Hm]].
    exists m. split; [exact Him |]. rewrite Str_nth_run1AsStates. exact Hm.
  Qed.

End lemma3b.


Section proof3.

  Variables AP F : Set.
  Variable f_to_f : F -> (list UnitInterval -> UnitInterval).

  Variable expression : ltl_f_expr AP F.
  Variable predicate : list UnitInterval.

  Let isSubExpr := isSubExpr AP F.
  Let isSubExpr_refl := isSubExpr_refl AP F.
  Let isSubExpr_trans := isSubExpr_trans AP F.
  Let isSubExpr_next_child := isSubExpr_next_child AP F.
  Let isSubExpr_until_child1 := isSubExpr_until_child1 AP F.
  Let isSubExpr_until_child2 := isSubExpr_until_child2 AP F.
  Let isSubExpr_FTerm_child := isSubExpr_FTerm_child AP F.

  Let consistent (state : ltl_f_expr AP F -> UnitInterval) :=
    (forall e, isSubExpr expression e ->
    (e = TRUE AP F -> state (e) = one) /\
    (e = FALSE AP F -> state (e) = zero) /\
    (forall p, e = AP_TERM AP F p -> (state (e) = zero \/ state (e) = one)) /\
    (forall f l, e = F_TERM AP F f l -> (state (e) = ((f_to_f f) (ListDef.map state l)))))
  .

  Let Alphabet := (AP -> AtomicProposition).
  Let State := {g : ltl_f_expr AP F -> UnitInterval | consistent g}.

  Let TransistionFunction (letter : Alphabet) (from : State) :=
    fun (to : State) => forall e, isSubExpr expression e -> (
    (forall ap, e = AP_TERM AP F ap -> ((letter ap = AP1 -> (proj1_sig from) e = one) /\ (letter ap = AP0 -> (proj1_sig from) e = zero))) /\
    (forall e1, e = (NEXT AP F e1) -> ((proj1_sig from) e = (proj1_sig to) (e1))) /\
    (forall e1 e2, e = (UNTIL AP F e1 e2) -> ((proj1_sig from) (UNTIL AP F e1 e2)) =
      unitinterval_max ((proj1_sig from) e2) (unitinterval_min ((proj1_sig from) e1) ((proj1_sig to) (UNTIL AP F e1 e2))))).

  Let IntialState (state: State) :=
    In ((proj1_sig state) expression) predicate.

  Let FinalState (e1 e2 : ltl_f_expr AP F) :=
    fun (state : State) => (proj1_sig state) (e2) = (proj1_sig state) (UNTIL AP F e1 e2).

  Let FinalStates (finalSet : State -> Prop) :=
    exists e1 e2, isSubExpr expression (UNTIL AP F e1 e2) /\ (FinalState e1 e2) = finalSet.

  Let sat_val := sat_val AP F f_to_f.
  Let satisfied_by_on := satisfied_by_on Alphabet State TransistionFunction IntialState FinalStates.


  Variable word : Stream (AP -> AtomicProposition).

  (* Sat val run *)
  CoFixpoint sat_val_run' (n : nat) : Stream (ltl_f_expr AP F -> UnitInterval) := 
    Cons (sat_val (nth_tail AP (INFINITE AP word) n)) (sat_val_run' (S n)).
  Definition sat_val_run := sat_val_run' 0.  

  Lemma sat_val_run'_nth_tl : forall m n,
    Str_nth_tl m (sat_val_run' n) = sat_val_run' (m + n).
  Proof.
    intros m. induction m as [| m IH]; intro n.
    - reflexivity.
    - simpl. replace (S (m + n))%nat with (m + S n)%nat by lia. apply IH.
  Qed.

  Lemma sat_val_run_correspond_to_ltl_f : forall expr : ltl_f_expr AP F, isSubExpr expression expr ->
    forall i : nat, Str_nth i sat_val_run expr = sat_val (nth_tail AP (INFINITE AP word) i) expr.
  Proof.
    intros expr _ i.
    unfold sat_val_run, Str_nth.
    rewrite sat_val_run'_nth_tl.
    rewrite Nat.add_0_r.
    reflexivity.
  Qed.

  Let if_satval_in_predicate_then_head_in_intial := 
    if_satval_in_predicate_then_head_in_intial AP F f_to_f expression predicate word sat_val_run sat_val_run_correspond_to_ltl_f.

  Let sat_val_run_as_states := run1AsStates AP F f_to_f expression word sat_val_run 
    sat_val_run_correspond_to_ltl_f.

  Let all_states_reachable_sat_val_run := all_states_reachable_run1 AP F f_to_f expression word sat_val_run
    sat_val_run_correspond_to_ltl_f.

  Let nbgwAcceptingRunsSatisfiesLtlFAtEveryI := nbgwAcceptingRunsSatisfiesLtlFAtEveryI AP F f_to_f expression
  predicate word.

  Lemma if_ngbw_ltl_f : forall run, satisfied_by_on word run -> 
    sat_val (nth_tail AP (INFINITE AP word) 0) expression = proj1_sig (hd run) expression.
  intros run H. assert ((Str_nth 0 run) = (hd run)) as Hobs. {
    unfold Str_nth. simpl. reflexivity.
  } rewrite <- Hobs.
  apply nbgwAcceptingRunsSatisfiesLtlFAtEveryI.
  + apply isSubExpr_refl.
  + apply H.
  Qed.

  Theorem proof3: In (sat_val (INFINITE AP word) expression) predicate <-> exists run,
    satisfied_by_on word run.
    split.
    + intros HsatVal. exists sat_val_run_as_states. split.
      - split.
        * apply if_satval_in_predicate_then_head_in_intial. apply HsatVal.
        * apply all_states_reachable_sat_val_run. 
      - apply run1VistsAllStatesInFinalStatesInfinitelyOften.
    + intros [run Hngbw]. pose proof Hngbw as Hngbw'. apply if_ngbw_ltl_f in Hngbw. simpl in Hngbw.
      rewrite Hngbw. destruct Hngbw' as [[Hinit Hreach] Hfinal]. unfold IntialState in Hinit. 
      assumption.
  Qed.

End proof3.

