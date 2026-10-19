From LTL_F_Project Require Import ltl_f.
From LTL_F_Project Require Import ngbw.
From LTL_F_Project Require Import utils.
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



Section proof2.

  Variables AP F : Set.
  Variable f_to_f : F -> (list UnitInterval -> UnitInterval).

  Let sat_val := sat_val AP F f_to_f.
  Let possible_statsfaction_values := possible_statsfaction_values AP F f_to_f.

  Definition possible_statsfaction_value_correct (e : ltl_f_expr AP F) := 
    forall (c: Computation AP), In (sat_val c e) (possible_statsfaction_values e).

  Theorem proof2 : forall (l : ltl_f_expr AP F ), possible_statsfaction_value_correct l. 
  Proof.
    intros l .
    induction l as [ | | ap | l f IH | e IH | e1 e2 IH] using ltl_f_induction_principle.
    + left. reflexivity.
    + left. reflexivity.
    + intros c. simpl. destruct (value_of_ap_at_time AP c ap 0).
      - assert (a = AP0 \/ a = AP1) as Ha by apply atomic_proposition_one_or_zero. destruct Ha as [Ha | Ha].
        * right. left. rewrite Ha. simpl. apply f_equal. apply proof_irrelevance.
        * left. rewrite Ha. simpl. apply f_equal. apply proof_irrelevance.
      - right. left. apply f_equal. apply proof_irrelevance.
    + intros c. simpl. 
      apply (possible_values_from_possible_args_correct _ (ListDef.map (fun item : ltl_f_expr AP F => sat_val c item) l)). apply cartesian_product_correct. 
      induction l as [ | x xs IHl].
      - constructor.
      - simpl. constructor.
        * apply IH. left. reflexivity.
        * apply IHl. intros x' Hx. apply IH. right. assumption.
      - reflexivity.
    + intros c. simpl. apply IH.
    + intros c. destruct IH as [IHe1 IHe2]. unfold possible_statsfaction_value_correct in IHe2.
      assert (Hspec : sat_val c (UNTIL AP F e1 e2) =
        match filter (until_is_achieved AP F sat_val c e1 e2) (until_candidates AP F f_to_f e1 e2) with
        | [] => zero
        | x :: xs => fold_left unitinterval_max xs x
        end) by reflexivity.
      assert (Hpsv : possible_statsfaction_values (UNTIL AP F e1 e2) = until_candidates AP F f_to_f e1 e2)
        by reflexivity.
      rewrite Hspec, Hpsv.
      assert (Hach : until_is_achieved AP F sat_val c e1 e2 (sat_val c e2) = true). {
      unfold until_is_achieved. destruct (ClassicalEpsilon.excluded_middle_informative _) as [Hp | Hnp].
      + reflexivity.
      + exfalso. apply Hnp. exists O. unfold until_candidate_le_e2_at_i. 
        unfold until_candidate_eq_e2_at_i_or_e1_before_i. 
        unfold until_candidate_le_all_e1_before_i. 
        rewrite nth_tail_0. repeat split.
        - apply Rle_refl.
        - left. reflexivity.
        - intros j Hj. lia.
       }
      assert (Hin_c : In (sat_val c e2) (until_candidates AP F f_to_f e1 e2)).
      { unfold until_candidates. apply in_or_app. right. exact (IHe2 c). }
      assert (Hin_filter : In (sat_val c e2) (filter (until_is_achieved AP F sat_val c e1 e2) (until_candidates AP F f_to_f e1 e2))).
      { apply filter_In. split; assumption. }
      destruct (filter (until_is_achieved AP F sat_val c e1 e2) (until_candidates AP F f_to_f e1 e2)) as [| x xs] eqn:Hf.
      - simpl in Hin_filter. contradiction.
      - assert (Hincl : incl (x :: xs) (until_candidates AP F f_to_f e1 e2)).
        { rewrite <- Hf. apply incl_filter. }
        apply Hincl. apply fold_left_max_in.
  Qed.

End proof2.

