(* begin hide *)
From Stdlib Require Import List.
From Stdlib Require Import Streams.
From Stdlib Require Import Reals.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.ClassicalEpsilon.
From LTL_F_Project Require Import utils.
Import ListNotations.
(* end hide *)

Open Scope R_scope.
Open Scope list_scope.

Section LTL_F.

Variables AP F : Set.
Context `{FiniteEnum AP} `{FiniteEnum F}.

Variable f_to_function : F -> (list UnitInterval -> UnitInterval).

Inductive Computation : Type  :=
  | FINITE (l : list (AP -> AtomicProposition))
  | INFINITE (s : Stream (AP -> AtomicProposition)).

Variable computation : Computation.

Inductive ltl_f_expr : Set :=
  | TRUE
  | FALSE
  | AP_TERM (p : AP)
  | F_TERM (f : F) (l : list ltl_f_expr)
  | NEXT (e' : ltl_f_expr)
  | UNTIL (e1 e2 :  ltl_f_expr).

Fixpoint sum_list_elements_nat (lengths : list nat) : nat :=
  match lengths with
  | nil => 0
  | x :: xs => x + sum_list_elements_nat xs
  end.

Lemma list_elem_lt_succ_sum_elems_nat : forall (l : list nat) (n : nat), In n l -> Nat.lt n (S (sum_list_elements_nat l)).
Proof.
  intros l n H1. 
  induction l.
  + inversion H1. 
  + destruct H1. 
    - subst a. simpl. lia.
    - apply IHl in H1. simpl. lia.
Qed.

Fixpoint expr_size (e : ltl_f_expr) : nat :=
  match e with
  | TRUE => 1
  | FALSE => 1
  | AP_TERM _ => 1
  | NEXT e1 => 1 + expr_size e1
  | UNTIL e1 e2 => 1 + expr_size e1 + expr_size e2
  | F_TERM f sub_exprs => 1 + sum_list_elements_nat (ListDef.map expr_size sub_exprs)
  end.

Theorem ltl_f_induction_principle : forall (P: ltl_f_expr -> Prop)
  (PTrue : P TRUE)
  (PFalse : P FALSE)
  (PAp_term : forall ap, P (AP_TERM ap))
  (PFTerm : forall l f , (forall x : ltl_f_expr, In x l -> P x) -> P (F_TERM f l))
  (PNext : forall e, (P e) -> P (NEXT e))
  (PUntil : forall e1 e2, (P e1) /\ (P e2) -> P (UNTIL e1 e2)), 
  forall e, P e.
Proof.
  intros.
  remember (expr_size e) as n_size eqn:Heq.
  generalize dependent e.
  induction n_size as [n_size IH] using lt_wf_ind.
  intros e Heq.
  destruct e.
  - apply PTrue.
  - apply PFalse.
  - apply PAp_term.
  - subst n_size. apply PFTerm. intros e H_in. apply (IH (expr_size e)). simpl. apply list_elem_lt_succ_sum_elems_nat . apply in_map. apply H_in.
    reflexivity.
  - subst n_size. apply PNext. apply (IH (expr_size e)). simpl. lia. reflexivity.
  - subst n_size. apply PUntil. split.
    + apply (IH (expr_size e1)). simpl. lia. reflexivity.
    + apply (IH (expr_size e2)). simpl. lia. reflexivity.
Qed.

Fixpoint cartesian_product {A : Type} (l : list (list A)) : list (list A) :=
  match l with
  | nil => [[]]
  | x :: xs => let rest := cartesian_product xs in
      concat (ListDef.map (fun e => ListDef.map (fun c => e :: c) rest) x)
  end.

Lemma cartesian_product_correct : forall {A : Type} (list_of_lists : list (list A)) (combination : list A),
  Forall2 (fun elem list => In elem list) combination list_of_lists  ->
  In combination (cartesian_product list_of_lists).
Proof.
  intros A list_of_lists. induction list_of_lists as [| x xs IH].
  - intros combination H1. inversion H1; subst.
    simpl. left. reflexivity.
  - intros combination H1. inversion H1 as [| y x1 ys] ; subst.
    simpl.
    apply in_concat.
    exists (ListDef.map (fun c : list A => y :: c) (cartesian_product xs)).
    split.
    + apply in_map_iff. exists y. split; [reflexivity | assumption].
    + apply in_map_iff. exists ys. split; [reflexivity |].
      apply IH. assumption.
Qed.

Fixpoint possible_values_from_possible_args (function: list UnitInterval  -> UnitInterval)
(args : list (list UnitInterval)) : list UnitInterval :=
match args with
| [] => [] 
| x :: xs => (function x) :: possible_values_from_possible_args function xs
end.

Lemma possible_values_from_possible_args_correct : forall (f : list UnitInterval -> UnitInterval) 
  (args : list UnitInterval) (possible_args : list (list UnitInterval)) (answer : UnitInterval),
  In args possible_args ->
  f args = answer ->
  In answer (possible_values_from_possible_args f possible_args).
Proof.
  intros f args possible_args answer H_in H_f.
  induction possible_args as [| x xs IH].
  - inversion H_in.
  - simpl. destruct H_in as [Heq | Hin].
    + subst x. rewrite H_f.
      simpl. left. reflexivity.
    + right. apply IH. apply Hin.
Qed.

Fixpoint possible_statsfaction_values (e : ltl_f_expr) : list UnitInterval := 
match e with 
  | TRUE => [one]
  | FALSE => [zero]
  | AP_TERM _ => [one; zero]
  | F_TERM f l => possible_values_from_possible_args (f_to_function f)
    (cartesian_product (ListDef.map possible_statsfaction_values l))
  | NEXT e1 => possible_statsfaction_values e1
  | UNTIL e1 e2 => (possible_statsfaction_values e1) ++ (possible_statsfaction_values e2)
end.

Fixpoint value_at_list_index (list : list (AP -> AtomicProposition)) (ap : AP) (time : nat) :=
 match time with 
 | O => match head list with 
        | Some x => Some ((x ap) )
        | None => None
end
 | S n => match tail list with 
          | [] => None
          | x => value_at_list_index x ap n 
          end
 end.

Definition value_of_ap_at_time (computation : Computation) (ap : AP) (time : nat) :=
  match computation with 
  | FINITE l => value_at_list_index l ap time
  | INFINITE s => Some (((Str_nth time s) ap))
  end.

Fixpoint nth_tail_list (list : list (AP -> AtomicProposition)) (index : nat) :=
  match list, index with
  | l, O => l
  | [], _ => [] 
  | x :: xs, S n => nth_tail_list  xs n
  end.

Definition nth_tail (computation : Computation) (index : nat) :=
  match computation with 
  | FINITE l => FINITE (nth_tail_list l index)
  | INFINITE s => INFINITE (Str_nth_tl index s)
  end.

Lemma nth_tail_0 : forall c, nth_tail c 0 = c.
Proof. intros [l | s]; [destruct l; reflexivity | reflexivity]. Qed.

Lemma nth_tail_list_add : forall (a b : nat) (l : list (AP -> AtomicProposition)),
  nth_tail_list (nth_tail_list l a) b = nth_tail_list l (a + b).
Proof.
  induction a as [| a' IHa]; intros b l.
  - destruct l as [| x xs]; simpl; reflexivity.
  - destruct l as [| x xs].
    + simpl. induction b; reflexivity.
    + simpl. apply IHa.
Qed.

Lemma nth_tail_add : forall c (a b : nat), nth_tail (nth_tail c a) b = nth_tail c (a + b).
Proof.
  intros [l | s] a b.
  - simpl. f_equal. apply nth_tail_list_add.
  - simpl. f_equal. rewrite Str_nth_tl_plus. f_equal. lia.
Qed.


Definition until_candidates (e1 e2 : ltl_f_expr) :=
  (possible_statsfaction_values e1) ++ (possible_statsfaction_values e2).

Definition until_candidate_le_e2_at_i 
  (sat_val : Computation -> ltl_f_expr -> UnitInterval) 
  (comp : Computation)
  (c : UnitInterval)
  (e2 : ltl_f_expr)
  (i : nat)
:= proj1_sig c <= proj1_sig (sat_val (nth_tail comp i) e2).

Definition until_candidate_eq_e2_at_i_or_e1_before_i
  (sat_val : Computation -> ltl_f_expr -> UnitInterval)
  (comp : Computation)
  (c : UnitInterval)
  (e2 : ltl_f_expr)
  (i : nat)
  (e1 : ltl_f_expr)
:= c = sat_val (nth_tail comp i) e2 \/ exists j : nat, (j < i)%nat /\ c = sat_val (nth_tail comp j) e1.

Definition until_candidate_le_all_e1_before_i
  (sat_val : Computation -> ltl_f_expr -> UnitInterval)
  (comp : Computation)
  (c : UnitInterval)
  (e1 : ltl_f_expr)
  (i : nat)
:= forall j : nat, (j < i)%nat -> proj1_sig c <= proj1_sig (sat_val (nth_tail comp j) e1).

Definition until_is_achieved (sat_val : Computation -> ltl_f_expr -> UnitInterval) (comp : Computation)
  (e1 e2 : ltl_f_expr) :=
  fun c => if excluded_middle_informative (
            exists i : nat,
              until_candidate_le_e2_at_i sat_val comp c e2 i /\
              until_candidate_eq_e2_at_i_or_e1_before_i sat_val comp c e2 i e1 /\
              until_candidate_le_all_e1_before_i sat_val comp c e1 i
           ) then true else false.


Fixpoint sat_val (c : Computation) (e : ltl_f_expr) : UnitInterval := 
  match e with 
  | TRUE => one
  | FALSE => zero
  | AP_TERM p => match value_of_ap_at_time c p 0 with
                  | Some x => atomic_to_unit  x
                  | None => zero
                 end
  | F_TERM f l => f_to_function f (ListDef.map (fun item => sat_val c item) l)
  | NEXT e' => sat_val (nth_tail c 1) e'
  | UNTIL e1 e2 =>
    match filter (until_is_achieved sat_val c e1 e2) (until_candidates e1 e2) with
    | [] => zero (* This wil never be empty since the value of e2 at 0 is always in the list*)
    | x :: xs => fold_left unitinterval_max xs x
    end
  end.

End LTL_F.

(* Declared here, after the section closes -- Arguments' simpl-behavior flags declared
   inside a still-open section do not survive End, so they must live out here to actually
   take effect for consumers of this file. Tells simpl/cbn it may always unfold these. *)
Arguments until_candidate_le_e2_at_i /.
Arguments until_candidate_eq_e2_at_i_or_e1_before_i /.
Arguments until_candidate_le_all_e1_before_i /.

Section Example.
Inductive AP : Type :=
  | Grant
  | Req.

Inductive F : Type :=
  | and
  | or.
  (*| not.*)

Import ListNotations.

(* 1. Define AP instances *)

Definition eqb_AP (x y : AP) : bool :=
  match x, y with
  | Grant, Grant => true
  | Req, Req => true
  | _, _ => false
  end.

Lemma eqb_AP_spec : forall x y : AP, eqb_AP x y = true <-> x = y.
Proof.
  destruct x, y; simpl; split; intro H; try discriminate; try reflexivity.
Qed.

Instance FiniteEnum_AP : FiniteEnum AP := {
  enum := [Grant; Req];
  enum_complete := fun x => match x with Grant => in_eq _ _ | Req => in_cons _ _ _ (in_eq _ _) end;
  eqb := eqb_AP;
  eqb_spec := eqb_AP_spec
}.

Definition eqb_F (x y : F) : bool :=
  match x, y with
  | and, and => true
  | or, or => true
  | _, _ => false
  end.

Lemma eqb_F_spec : forall x y : F, eqb_F x y = true <-> x = y.
Proof.
  destruct x, y; simpl; split; intro H; try discriminate; try reflexivity.
Qed.

(* Register F as a FiniteEnum *)
Instance FiniteEnum_F : FiniteEnum F := {
  enum := [and; or];
  enum_complete := fun x => match x with and => in_eq _ _ | or => in_cons _ _ _ (in_eq _ _) end;
  eqb := eqb_F;
  eqb_spec := eqb_F_spec
}.

Definition and_func (x y : UnitInterval) : UnitInterval  := 
  if Rle_dec (proj1_sig x) (proj1_sig y) then x else y.

Definition or_func (x y : UnitInterval) : UnitInterval   :=
  if Rle_dec (proj1_sig x) (proj1_sig y) then y else x.

(*Definition not_func (x : UnitInterval) : UnitInterval := 1 - (proj1_sig x).*)

Definition f_to_function (f : F) : (list UnitInterval  -> UnitInterval ) :=
  match f with 
  | and => fun l => 
      match l with
      | x :: y :: _ => and_func x y
      | _ => zero 
      end
  | or => fun l => 
      match l with
      | x :: y :: _ => or_func x y
      | _ => zero 
      end
  end.

Definition system_values_at_0 (p : AP) : (AtomicProposition) :=
  match p with
  | Grant => AP0
  | Req => AP1
  end.

Definition system_values_at_1 (p : AP) : (AtomicProposition) :=
  match p with
  | Grant => AP1
  | Req => AP0
  end.

Definition computation : Computation AP := FINITE AP (system_values_at_0 :: system_values_at_1 :: nil).

Definition concrete_sat_val := sat_val AP F f_to_function.

Definition C_TRUE := TRUE AP F.
Definition C_FALSE := FALSE AP F.
Definition C_F_TERM := F_TERM AP F.
Definition C_AP_TERM := AP_TERM AP F.
Definition C_NEXT := NEXT AP F.

Eval compute in and_func zero one.

Example test : concrete_sat_val  computation C_TRUE = one.
Proof. 
   reflexivity.
Qed.

Example test2 : concrete_sat_val computation (C_F_TERM and (C_TRUE :: C_FALSE :: nil)) = zero.
Proof.
  simpl. unfold and_func. destruct (Rle_dec 1 0).
    - apply Rle_not_lt in r. assert (0 < 1). apply Rlt_0_1. contradiction.
    - simpl. destruct (Rle_dec 1 0) as [H|H].
      * contradiction. 
      * reflexivity.
Qed.

Example test3 : concrete_sat_val computation (C_F_TERM or (C_AP_TERM Grant :: C_NEXT (C_AP_TERM Grant) :: nil)) = one.
Proof.
  simpl. unfold or_func. simpl. destruct (Rle_dec 0 1) as [H | H].
  - apply f_equal. apply proof_irrelevance.
  - apply Rnot_le_lt in H. assert (1 < 1). apply (Rlt_trans _ 0 _). apply H. apply Rlt_0_1. apply Rlt_irrefl in H0. contradiction.
Qed.

CoFixpoint ap_stream : Stream (AP -> AtomicProposition) := Cons system_values_at_0 co_ap_stream
with co_ap_stream : Stream (AP -> AtomicProposition) := Cons system_values_at_1 ap_stream.

Definition infinite_computation : Computation AP := INFINITE AP (ap_stream).

Example test4 : concrete_sat_val infinite_computation (C_F_TERM or (C_AP_TERM Grant :: C_NEXT (C_AP_TERM Grant) :: nil)) = one.
Proof.
  + simpl. unfold or_func. simpl. destruct (Rle_dec 0 1) as [H | H].
    - apply f_equal. apply proof_irrelevance.
    - apply Rnot_le_lt in H. assert (1 < 1). apply (Rlt_trans _ 0 _). apply H. apply Rlt_0_1. apply Rlt_irrefl in H0. contradiction.
Qed.

End Example.
