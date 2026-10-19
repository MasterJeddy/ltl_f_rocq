From LTL_F_Project Require Import utils.
From LTL_F_Project Require Import ltl_f.
From LTL_F_Project Require Import nbgw_for_ltl_f.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.


Section psv_bound.

  Variables AP F : Set.
  Variable f_to_f : F -> (list UnitInterval -> UnitInterval).

  Let possible_statsfaction_values := possible_statsfaction_values AP F f_to_f.
  Let expr_size := expr_size AP F.

  Lemma length_possible_values_from_possible_args : forall f args,
    length (possible_values_from_possible_args f args) = length args.
    intros f args. induction args as [| arg args' IH].
    + simpl. reflexivity.
    + simpl. f_equal. apply IH.
  Qed.

  Lemma list_sum_const : forall {A : Type} (l : list A) (n : nat),
    list_sum (map (fun _ => n) l) = (length l * n)%nat.
  Proof.
    intros A l n. induction l as [| a l IH]; simpl; [reflexivity | lia].
  Qed.

  Lemma length_cartesian_product : forall {A : Type} (l : list (list A)),
    length (cartesian_product l) = fold_right Nat.mul 1 (map (@length A) l).
  Proof.
    intros A l. induction l as [| x xs IH].
    - reflexivity.
    - simpl. rewrite length_concat. rewrite map_map.
      rewrite map_ext with (g := fun _ => length (cartesian_product xs)).
      + rewrite list_sum_const. rewrite IH. reflexivity.
      + intros e. apply length_map.
  Qed.

  Lemma prod_pow_two : forall l: list nat,
    (fold_right Nat.mul 1 (ListDef.map (fun n => 2 ^ n) l)
     = 2 ^ sum_list_elements_nat l)%nat.
  intros l. induction l as [ | x xs IH].
  + simpl. reflexivity.
  + simpl. rewrite IH. symmetry. apply Nat.pow_add_r.
  Qed.

  Lemma fold_right_mul_le : forall {A : Type} (f g : A -> nat) (l : list A),
    (forall x, In x l -> f x <= g x) ->
    fold_right Nat.mul 1 (map f l) <= fold_right Nat.mul 1 (map g l).
  Proof.
    intros A f g l. induction l as [| a l IH]; intros Hle; simpl.
    - reflexivity.
    - apply Nat.mul_le_mono.
      + apply Hle. left. reflexivity.
      + apply IH. intros x Hx. apply Hle. right. assumption.
  Qed.

  Theorem possible_statsfaction_values_bounded : forall e : ltl_f_expr AP F,
    (length (possible_statsfaction_values e) <= 2 ^ expr_size e).
  induction e as [ | | ap | l f IH | e IH | e1 e2 IH] using ltl_f_induction_principle.
  + simpl. lia.
  + simpl. lia.
  + simpl. lia.
  + unfold expr_size. simpl. rewrite length_possible_values_from_possible_args. 
    rewrite length_cartesian_product. rewrite map_map. 
    apply Nat.le_trans with (m := fold_right Nat.mul 1 (map (fun x => 2 ^ ltl_f.expr_size AP F x) l)).
     * apply fold_right_mul_le. intros x Hx. apply IH. assumption.
     * rewrite <- map_map with (f := ltl_f.expr_size AP F) (g := fun n => 2 ^ n).
        rewrite prod_pow_two. lia.
  + simpl. rewrite IH. lia.
  + simpl. destruct IH as [IHe1 IHe2]. rewrite length_app. 
    rewrite Nat.pow_add_r.
    assert (H1 : 1 <= 2 ^ expr_size e1) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    assert (H2 : 1 <= 2 ^ expr_size e2) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    nia.
  Qed.
End psv_bound.

Section states_bound.
  Variables AP F : Set.
  Variables f_to_f : F -> (list UnitInterval -> UnitInterval ).
  Variable expression : ltl_f_expr AP F.

  Local Notation psv := (possible_statsfaction_values AP F f_to_f). 
  Local Notation size := (expr_size AP F).
  Local Notation isSub := (isSubExpr AP F).
  Local Notation consistent := (consistent AP F f_to_f expression).
  Local Notation isSubExpr_FTerm_child := (isSubExpr_FTerm_child AP F).
  Local Notation isSub_trans := (isSubExpr_trans AP F).

  (* General lemmas *)

  Lemma list_sum_is_sum_list_elements_nat : forall l : list nat,
    list_sum l = sum_list_elements_nat l.
  induction l as [| x xs IH]; simpl; [reflexivity | rewrite IH; reflexivity ].
  Qed.

  Lemma list_sum_map_le : forall {A : Type} (f g : A -> nat) (l : list A),
    (forall x, In x l -> f x <= g x) ->
    list_sum (map f l) <= list_sum (map g l).
   intros A f g l. induction l as [ | a L IH].
   + reflexivity.
   + intros Hle. simpl. apply Nat.add_le_mono. 
    - apply Hle. left. reflexivity.
    - apply IH. intros x Hx. apply Hle. right. assumption.
  Qed.

  Lemma fold_right_mul_const : forall {A : Type} (c : nat) (l : list A),
    fold_right Nat.mul 1 (map (fun _ => c) l) = c ^ length l.
  Proof.
    intros A c l. induction l as [| a l IH]; simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma map_eq_pointwise : forall {A B : Type} (f g : A -> B) (l : list A),
    map f l = map g l -> forall x, In x l -> f x = g x.
  Proof.
    intros A B f g l. induction l as [| a l IH]; intros Heq x Hin.
    - inversion Hin.
    - simpl in Heq. injection Heq as Hhd Htl.
      destruct Hin as [<- | Hin]; [assumption | apply IH; assumption].
  Qed.

  (* Sub expression *)
  Fixpoint sub_exprs (e : ltl_f_expr AP F) : list (ltl_f_expr AP F) :=
    match e with
    | TRUE _ _        => [TRUE AP F]
    | FALSE _ _       => [FALSE AP F]
    | AP_TERM _ _ p   => [AP_TERM AP F p]
    | F_TERM _ _ f l  => F_TERM AP F f l :: concat (ListDef.map sub_exprs l)
    | NEXT _ _ e1     => NEXT AP F e1 :: sub_exprs e1
    | UNTIL _ _ e1 e2 => UNTIL AP F e1 e2 :: (sub_exprs e1 ++ sub_exprs e2)
    end.

  Lemma sub_exprs_sound : forall e x, In x (sub_exprs e) -> isSub e x.
  Proof.
    intros e. induction e as [ | | ap | l f IH | e IH | e1 e2 IH] using ltl_f_induction_principle;
      intros x Hin; simpl in Hin.
    - destruct Hin as [<- | []]. reflexivity.
    - destruct Hin as [<- | []]. reflexivity.
    - destruct Hin as [<- | []]. reflexivity.
    - destruct Hin as [<- | Hin].
      + simpl. left. reflexivity.
      + apply in_concat in Hin as [ll [Hll Hx]].
        apply in_map_iff in Hll as [y [<- Hy]].
        simpl. right. apply or_list_of_props_exists. exists y. split; [assumption |].
        apply IH; assumption.
    - destruct Hin as [<- | Hin].
      + simpl. left. reflexivity.
      + simpl. right. apply IH. assumption.
    - destruct IH as [IH1 IH2]. destruct Hin as [<- | Hin].
      + simpl. left. reflexivity.
      + apply in_app_or in Hin as [Hin | Hin]; simpl; right; [left | right]; auto.
  Qed.

  Lemma sub_exprs_complete : forall e x, isSub e x -> In x (sub_exprs e).
  Proof.
    intros e. induction e as [ | | ap | l f IH | e IH | e1 e2 IH] using ltl_f_induction_principle;
      intros x Hsub; simpl in Hsub; simpl.
    - subst x. left. reflexivity.
    - subst x. left. reflexivity.
    - subst x. left. reflexivity.
    - destruct Hsub as [-> | Hor]; [left; reflexivity | right].
      apply or_list_of_props_exists in Hor as [y [Hy Hsy]].
      apply in_concat. exists (sub_exprs y). split.
      + apply in_map. assumption.
      + apply IH; assumption.
    - destruct Hsub as [-> | Hsub]; [left; reflexivity | right; apply IH; assumption].
    - destruct IH as [IH1 IH2]. destruct Hsub as [-> | [Hsub | Hsub]];
        [left; reflexivity
        | right; apply in_or_app; left; apply IH1; assumption
        | right; apply in_or_app; right; apply IH2; assumption].
  Qed.

  Lemma sub_exprs_size_mono : forall e x, In x (sub_exprs e) -> size x <= size e.
  Proof.
    intros e. induction e as [ | | ap | l f IH | e IH | e1 e2 IH] using ltl_f_induction_principle;
      intros x Hin; simpl in Hin.
    - destruct Hin as [<- | []]. reflexivity.
    - destruct Hin as [<- | []]. reflexivity.
    - destruct Hin as [<- | []]. reflexivity.
    - destruct Hin as [<- | Hin]; [reflexivity |].
      apply in_concat in Hin as [ll [Hll Hx]].
      apply in_map_iff in Hll as [y [<- Hy]].
      apply Nat.le_trans with (m := size y); [apply IH; assumption |].
      simpl.
      assert (In (size y) (ListDef.map (expr_size AP F) l)) by (apply in_map; assumption).
      apply list_elem_lt_succ_sum_elems_nat in H. lia.
    - destruct Hin as [<- | Hin]; [reflexivity |].
      apply IH in Hin. simpl. lia.
    - destruct IH as [IH1 IH2]. destruct Hin as [<- | Hin]; [reflexivity |].
      apply in_app_or in Hin as [Hin | Hin]; [apply IH1 in Hin | apply IH2 in Hin]; simpl; lia.
  Qed.

  Lemma sub_exprs_length : forall e, length (sub_exprs e) <= size e.
  Proof.
    intros e. induction e as [ | | ap | l f IH | e IH | e1 e2 IH] using ltl_f_induction_principle.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - simpl. apply le_n_S.
      rewrite length_concat. rewrite map_map.
      rewrite list_sum_is_sum_list_elements_nat.
      rewrite <- list_sum_is_sum_list_elements_nat.
      apply list_sum_map_le. intros x Hx. apply IH. assumption.
    - simpl. lia.
    - destruct IH as [IH1 IH2]. simpl. rewrite length_app. lia.
  Qed.

  Definition state_table (g : ltl_f_expr AP F -> UnitInterval) : list UnitInterval :=
    ListDef.map g (sub_exprs expression).

  Definition valued_in_psv (g : ltl_f_expr AP F -> UnitInterval) :=
    forall e, isSub expression e -> In (g e) (psv e).

  Lemma state_table_eq_iff : forall g h,
    state_table g = state_table h <-> (forall e, isSub expression e -> g e = h e).
  Proof.
    intros g h. unfold state_table. split.
    - intros Heq e Hsub.
      apply (map_eq_pointwise g h (sub_exprs expression) Heq).
      apply sub_exprs_complete. assumption.
    - intros Hall. apply map_ext_in. intros x Hx.
      apply Hall. apply sub_exprs_sound. assumption.
  Qed.

  (* ==================================================================== *)
  (*  Explicit enumeration of the consistent states, in the style of      *)
  (*  possible_statsfaction_values / proof2.                              *)
  (* ==================================================================== *)

  Definition table_root (t : list UnitInterval) : UnitInterval := hd zero t.

  Fixpoint possible_state_tables (e : ltl_f_expr AP F) : list (list UnitInterval) :=
    match e with
    | TRUE _ _        => [[one]]
    | FALSE _ _       => [[zero]]
    | AP_TERM _ _ _   => [[zero]; [one]]
    | F_TERM _ _ f l  =>
        ListDef.map (fun ts => f_to_f f (ListDef.map table_root ts) :: concat ts)
                    (cartesian_product (ListDef.map possible_state_tables l))
    | NEXT _ _ e1     =>
        ListDef.map (fun p => fst p :: snd p)
                    (list_prod (psv (NEXT AP F e1)) (possible_state_tables e1))
    | UNTIL _ _ e1 e2 =>
        ListDef.map (fun p => fst p :: (fst (snd p) ++ snd (snd p)))
                    (list_prod (psv (UNTIL AP F e1 e2))
                               (list_prod (possible_state_tables e1)
                                          (possible_state_tables e2)))
    end.

  (* ---------- the table of a state, and the two paper side conditions ---------- *)

  Lemma sub_exprs_head : forall e, exists r, sub_exprs e = e :: r.
  Proof. intros e; destruct e; simpl; eexists; reflexivity. Qed.

  Lemma table_root_table : forall g e, table_root (ListDef.map g (sub_exprs e)) = g e.
  Proof.
    intros g e. destruct (sub_exprs_head e) as [r Hr]. rewrite Hr. reflexivity.
  Qed.

  Definition consistent_at (e : ltl_f_expr AP F) :=
    nbgw_for_ltl_f.consistent AP F f_to_f e.

  Definition valued_at (e : ltl_f_expr AP F) (g : ltl_f_expr AP F -> UnitInterval) :=
    forall x, isSub e x -> In (g x) (psv x).

  Lemma consistent_at_sub : forall e e' g,
    isSub e e' -> consistent_at e g -> consistent_at e' g.
  Proof.
    intros e e' g Hsub Hc x Hx. apply Hc. eapply isSub_trans; eassumption.
  Qed.

  Lemma valued_at_sub : forall e e' g,
    isSub e e' -> valued_at e g -> valued_at e' g.
  Proof.
    intros e e' g Hsub Hv x Hx. apply Hv. eapply isSub_trans; eassumption.
  Qed.

  Lemma Forall2_map_map : forall {A B} (f : A -> B) (h : A -> list B) (l : list A),
    (forall x, In x l -> In (f x) (h x)) ->
    Forall2 (fun elem lst => In elem lst) (ListDef.map f l) (ListDef.map h l).
  Proof.
    intros A B f h l. induction l as [| x xs IH]; intros Hall; simpl.
    - constructor.
    - constructor; [apply Hall; left; reflexivity |].
      apply IH. intros y Hy. apply Hall. right. assumption.
  Qed.

  (* ---------- correctness: every consistent, psv-valued state is enumerated ---------- *)

  Theorem possible_state_tables_correct : forall e g,
    consistent_at e g -> valued_at e g ->
    In (ListDef.map g (sub_exprs e)) (possible_state_tables e).
  Proof.
    intros e. induction e as [ | | ap | l f IH | e1 IH | e1 e2 IH]
      using ltl_f_induction_principle; intros g Hc Hv.
    - destruct (Hc (TRUE AP F) (isSubExpr_refl AP F _)) as [Ht _].
      simpl. rewrite (Ht eq_refl). left. reflexivity.
    - destruct (Hc (FALSE AP F) (isSubExpr_refl AP F _)) as [_ [Hf _]].
      simpl. rewrite (Hf eq_refl). left. reflexivity.
    - destruct (Hc (AP_TERM AP F ap) (isSubExpr_refl AP F _)) as [_ [_ [Hap _]]].
      simpl. destruct (Hap ap eq_refl) as [H0 | H1]; rewrite ?H0, ?H1.
      + left. reflexivity.
      + right. left. reflexivity.
    - destruct (Hc (F_TERM AP F f l) (isSubExpr_refl AP F _)) as [_ [_ [_ Hft]]].
      simpl. apply in_map_iff.
      exists (ListDef.map (fun ei => ListDef.map g (sub_exprs ei)) l). split.
      + rewrite map_map.
        rewrite (map_ext _ g) by (intros ei; apply table_root_table).
        rewrite <- (Hft f l eq_refl).
        f_equal. rewrite concat_map, map_map. reflexivity.
      + apply cartesian_product_correct. apply Forall2_map_map.
        intros x Hx. apply IH; [assumption | | ].
        * eapply consistent_at_sub; [apply isSubExpr_FTerm_child; exact Hx | exact Hc].
        * eapply valued_at_sub; [apply isSubExpr_FTerm_child; exact Hx | exact Hv].
    - simpl. apply in_map_iff.
      exists (g (NEXT AP F e1), ListDef.map g (sub_exprs e1)). split.
      + reflexivity.
      + apply in_prod.
        * exact (Hv (NEXT AP F e1) (isSubExpr_refl AP F _)).
        * apply IH.
          -- eapply consistent_at_sub; [apply isSubExpr_next_child | exact Hc].
          -- eapply valued_at_sub; [apply isSubExpr_next_child | exact Hv].
    - destruct IH as [IH1 IH2]. simpl. apply in_map_iff.
      exists (g (UNTIL AP F e1 e2),
              (ListDef.map g (sub_exprs e1), ListDef.map g (sub_exprs e2))). split.
      + simpl. f_equal. rewrite map_app. reflexivity.
      + apply in_prod; [exact (Hv (UNTIL AP F e1 e2) (isSubExpr_refl AP F _)) |].
        apply in_prod.
        * apply IH1.
          -- eapply consistent_at_sub; [apply isSubExpr_until_child1 | exact Hc].
          -- eapply valued_at_sub; [apply isSubExpr_until_child1 | exact Hv].
        * apply IH2.
          -- eapply consistent_at_sub; [apply isSubExpr_until_child2 | exact Hc].
          -- eapply valued_at_sub; [apply isSubExpr_until_child2 | exact Hv].
  Qed.

  (* ---------- the enumeration is bounded ---------- *)

  Lemma sum_sq_le_sq_sum : forall {A} (f : A -> nat) (l : list A),
    sum_list_elements_nat (ListDef.map (fun x => f x ^ 2) l)
    <= (sum_list_elements_nat (ListDef.map f l)) ^ 2.
  Proof.
    intros A f l. induction l as [| a l IH]; simpl.
    - lia.
    - apply Nat.le_trans
        with (m := f a ^ 2 + (sum_list_elements_nat (ListDef.map f l)) ^ 2).
      + apply Nat.add_le_mono_l. exact IH.
      + rewrite ?Nat.pow_2_r. nia.
  Qed.

  Theorem possible_state_tables_bounded : forall e,
    length (possible_state_tables e) <= 2 ^ (size e ^ 2).
  Proof.
    intros e. induction e as [ | | ap | l f IH | e1 IH | e1 e2 IH]
      using ltl_f_induction_principle.
    - simpl. lia.
    - simpl. lia.
    - simpl. lia.
    - cbn [possible_state_tables].
      rewrite length_map, length_cartesian_product, map_map.
      apply Nat.le_trans with
        (m := fold_right Nat.mul 1 (ListDef.map (fun x => 2 ^ (size x ^ 2)) l)).
      + apply fold_right_mul_le. intros x Hx. apply IH. assumption.
      + rewrite <- map_map with (f := fun x => size x ^ 2) (g := fun n => 2 ^ n).
        rewrite prod_pow_two. apply Nat.pow_le_mono_r; [lia |].
        apply Nat.le_trans with (m := (sum_list_elements_nat (ListDef.map size l)) ^ 2).
        * apply sum_sq_le_sq_sum.
        * replace (size (F_TERM AP F f l))
            with (1 + sum_list_elements_nat (ListDef.map size l)) by reflexivity.
          rewrite ?Nat.pow_2_r. nia.
    - cbn [possible_state_tables].
      rewrite length_map, length_prod.
      apply Nat.le_trans with (m := 2 ^ size (NEXT AP F e1) * 2 ^ (size e1 ^ 2)).
      + apply Nat.mul_le_mono; [apply possible_statsfaction_values_bounded | exact IH].
      + rewrite <- Nat.pow_add_r. apply Nat.pow_le_mono_r; [lia |].
        replace (size (NEXT AP F e1)) with (1 + size e1) by reflexivity.
        rewrite ?Nat.pow_2_r. nia.
    - destruct IH as [IH1 IH2].
      cbn [possible_state_tables].
      rewrite length_map, length_prod, length_prod.
      apply Nat.le_trans with
        (m := 2 ^ size (UNTIL AP F e1 e2) * (2 ^ (size e1 ^ 2) * 2 ^ (size e2 ^ 2))).
      + apply Nat.mul_le_mono; [apply possible_statsfaction_values_bounded |].
        apply Nat.mul_le_mono; assumption.
      + rewrite <- Nat.pow_add_r, <- Nat.pow_add_r.
        apply Nat.pow_le_mono_r; [lia |].
        replace (size (UNTIL AP F e1 e2)) with (1 + size e1 + size e2) by reflexivity.
        rewrite ?Nat.pow_2_r. nia.
  Qed.

  (* ---------- the bound on the states themselves ---------- *)

  Theorem state_table_in_possible : forall g,
    consistent g -> valued_in_psv g -> In (state_table g) (possible_state_tables expression).
  Proof.
    intros g Hc Hv. unfold state_table.
    apply possible_state_tables_correct; assumption.
  Qed.

  Theorem consistent_states_bounded :
    forall L : list (ltl_f_expr AP F -> UnitInterval),
      (forall g, In g L -> consistent g) ->
      (forall g, In g L -> valued_in_psv g) ->
      NoDup (ListDef.map state_table L) ->
      length L <= 2 ^ (size expression ^ 2).
  Proof.
    intros L Hc Hv Hnodup.
    rewrite <- (length_map state_table L).
    apply Nat.le_trans with (m := length (possible_state_tables expression));
      [| apply possible_state_tables_bounded].
    apply NoDup_incl_length; [assumption |].
    intros t Ht. apply in_map_iff in Ht as [g [<- Hg]].
    apply state_table_in_possible; [apply Hc | apply Hv]; assumption.
  Qed.

  Definition PaperState : Set :=
    { g : ltl_f_expr AP F -> UnitInterval | consistent g /\ valued_in_psv g }.

  Theorem PaperState_bounded :
    forall L : list PaperState,
      NoDup (ListDef.map (fun s => state_table (proj1_sig s)) L) ->
      length L <= 2 ^ (size expression ^ 2).
  Proof.
    intros L Hnodup.
    pose proof (consistent_states_bounded
                  (ListDef.map (@proj1_sig (ltl_f_expr AP F -> UnitInterval) _) L)) as Hb.
    rewrite length_map in Hb. apply Hb.
    - intros g Hg. apply in_map_iff in Hg as [s [<- _]].
      exact (proj1 (proj2_sig s)).
    - intros g Hg. apply in_map_iff in Hg as [s [<- _]].
      exact (proj2 (proj2_sig s)).
    - rewrite map_map. exact Hnodup.
  Qed.

  Local Notation State       := (nbgw_for_ltl_f.State AP F f_to_f expression).
  Local Notation FinalState  := (nbgw_for_ltl_f.FinalState AP F f_to_f expression).
  Local Notation FinalStates := (nbgw_for_ltl_f.FinalStates AP F f_to_f expression).

  (* The (e1, e2) pairs of every UNTIL subexpression. *)
  Fixpoint until_pairs (e : ltl_f_expr AP F) : list (ltl_f_expr AP F * ltl_f_expr AP F) :=
    match e with
    | TRUE _ _        => []
    | FALSE _ _       => []
    | AP_TERM _ _ _   => []
    | F_TERM _ _ f l  => concat (ListDef.map until_pairs l)
    | NEXT _ _ e1     => until_pairs e1
    | UNTIL _ _ e1 e2 => (e1, e2) :: (until_pairs e1 ++ until_pairs e2)
    end.

  Definition finalSets : list (State -> Prop) :=
    ListDef.map (fun p => FinalState (fst p) (snd p)) (until_pairs expression).

  Lemma until_pairs_complete : forall e e1 e2,
    isSub e (UNTIL AP F e1 e2) -> In (e1, e2) (until_pairs e).
  Proof.
    intros e. induction e as [ | | ap | l f IH | e' IH | a b IH]
      using ltl_f_induction_principle; intros e1 e2 Hsub; simpl in Hsub.
    - discriminate Hsub.
    - discriminate Hsub.
    - discriminate Hsub.
    - destruct Hsub as [Heq | Hor]; [discriminate Heq |].
      apply or_list_of_props_exists in Hor as [y [Hy Hsy]].
      cbn [until_pairs]. apply in_concat. exists (until_pairs y).
      split; [apply in_map; assumption | apply IH; assumption].
    - destruct Hsub as [Heq | Hsub]; [discriminate Heq |].
      cbn [until_pairs]. apply IH. assumption.
    - destruct IH as [IH1 IH2]. cbn [until_pairs].
      destruct Hsub as [Heq | [Hsub | Hsub]].
      + injection Heq as Ha Hb. subst. left. reflexivity.
      + right. apply in_or_app. left.  apply IH1. assumption.
      + right. apply in_or_app. right. apply IH2. assumption.
  Qed.

  Lemma until_pairs_length : forall e, length (until_pairs e) <= size e.
  Proof.
    intros e. induction e as [ | | ap | l f IH | e' IH | a b IH]
      using ltl_f_induction_principle.
    - simpl. lia.
    - simpl. lia.
    - simpl. lia.
    - cbn [until_pairs expr_size].
      rewrite length_concat, map_map.
      apply Nat.le_trans with (m := sum_list_elements_nat (ListDef.map size l)); [| lia].
      apply list_sum_map_le. intros x Hx. apply IH. assumption.
    - cbn [until_pairs expr_size]. lia.
    - destruct IH as [IH1 IH2]. simpl. rewrite length_app. lia.
  Qed.

  Theorem finalSets_complete : forall s, FinalStates s -> In s finalSets.
    intros s [e1 [e2 [Hsub Heq]]]. unfold finalSets.
    rewrite <- Heq.
    apply (in_map (fun p => FinalState (fst p) (snd p)) (until_pairs expression) (e1, e2)).
    apply until_pairs_complete. assumption.
  Qed.

  Theorem finalSets_length : length finalSets <= size expression.
    unfold finalSets. rewrite length_map. apply until_pairs_length.
  Qed.

  Theorem finalStates_bounded :
    forall L : list (State -> Prop),
      (forall s, In s L -> FinalStates s) ->
      NoDup L ->
      length L <= size expression.
    intros L Hfin Hnodup.
    apply Nat.le_trans with (m := length finalSets); [| apply finalSets_length].
    apply NoDup_incl_length; [assumption |].
    intros s Hs. apply finalSets_complete. apply Hfin. assumption.
  Qed.

  Theorem finalStates_bounded_exists :
    exists L : list (State -> Prop),
      length L <= size expression /\ (forall s, FinalStates s -> In s L).
    exists finalSets. split; [apply finalSets_length | apply finalSets_complete].
  Qed.

End states_bound.
