From Stdlib Require Import Relations.
From Stdlib Require Import Streams.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Reals.
From Stdlib Require Import Classical.
From Stdlib Require Import Logic.ProofIrrelevance.
From LTL_F_Project Require Import ltl_f.
From LTL_F_Project Require Import utils.
From LTL_F_Project Require Import proof2.
From LTL_F_Project Require Import until_lemmas.

Import ListNotations.
Open Scope R_scope.

Section ltl.
  Variable (AP : Set).

  (* syntax *)
  Inductive ltl_expr := 
    | TRUE
    | FALSE
    | AP_TERM (p : AP)
    | AND (e1 : ltl_expr) (e2 : ltl_expr)
    | OR (e1 : ltl_expr) (e2 : ltl_expr)
    | NOT (e' : ltl_expr) 
    | NEXT (e' : ltl_expr)
    | UNTIL (e1 : ltl_expr) (e2 : ltl_expr).

  Fixpoint ltl_sat (c : Computation AP) (e : ltl_expr) : Prop :=
    match e with
    | TRUE  => True
    | FALSE => False
    | AP_TERM p => value_of_ap_at_time AP c p 0 = Some AP1
    | AND e1 e2 => ltl_sat c e1 /\ ltl_sat c e2
    | OR e1 e2 => ltl_sat c e1 \/ ltl_sat c e2
    | NOT e' => ~ ltl_sat c e'
    | NEXT e' => ltl_sat (nth_tail AP c 1) e'
    | UNTIL e1 e2 => exists i : nat, ltl_sat (nth_tail AP c i) e2 /\ forall j : nat, (j < i)%nat -> ltl_sat (nth_tail AP c j) e1
    end.

  (** The length of a formula, counted as its number of nodes.  Used for the
      size bounds at the end of the file. *)
  Fixpoint ltl_size (e : ltl_expr) : nat :=
    match e with
    | TRUE | FALSE | AP_TERM _ => 1
    | AND e1 e2 => 1 + ltl_size e1 + ltl_size e2
    | OR e1 e2 => 1 + ltl_size e1 + ltl_size e2
    | NOT e' => 1 + ltl_size e'
    | NEXT e' => 1 + ltl_size e'
    | UNTIL e1 e2 => 1 + ltl_size e1 + ltl_size e2
    end.

End ltl.

(** ** Generic helpers *)

(** [1 - x], the De Morgan dual used to interpret [NOT] inside [ltl_f]. *)
Lemma unitinterval_comp_proof : forall x : UnitInterval, 0 <= 1 - proj1_sig x <= 1.
Proof. intros [r [Hlo Hhi]]. simpl. lra. Qed.

Definition unitinterval_comp (x : UnitInterval) : UnitInterval :=
  exist _ (1 - proj1_sig x) (unitinterval_comp_proof x).

(** Pointwise application of a list of functions to a list of arguments.  Kept
    outside [ge_ltl] so that the recursive calls there all sit under a plain
    [map] over the subformula list, which is the shape [sat_val] itself uses
    and which the guard checker accepts. *)
Fixpoint zip_apply {A B : Type} (fs : list (A -> B)) (xs : list A) : list B :=
  match fs, xs with
  | f :: fs', x :: xs' => f x :: zip_apply fs' xs'
  | _, _ => []
  end.

Lemma zip_apply_length : forall {A B : Type} (fs : list (A -> B)) (xs : list A),
  length fs = length xs -> length (zip_apply fs xs) = length fs.
Proof.
  intros A B fs. induction fs as [| f fs' IH]; intros [| x xs'] Hlen;
    simpl in *; try discriminate; try reflexivity.
  rewrite IH by lia. reflexivity.
Qed.

(** Zipping two lists that were both produced from the same source list
    collapses to a single [map]. *)
Lemma zip_apply_map_map : forall {A B C : Type} (g : A -> B -> C) (h : A -> B) (l : list A),
  zip_apply (ListDef.map g l) (ListDef.map h l) = ListDef.map (fun x => g x (h x)) l.
Proof.
  intros A B C g h l. induction l as [| x xs IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.


(** Every tuple drawn from a cartesian product has one component per operand. *)
Lemma cartesian_product_length : forall {A : Type} (ls : list (list A)) (args : list A),
  In args (cartesian_product ls) -> length args = length ls.
Proof.
  intros A ls. induction ls as [| x xs IH]; intros args Hin.
  - simpl in Hin. destruct Hin as [Heq | []]. subst args. reflexivity.
  - simpl in Hin. apply in_concat in Hin as [sub [Hsub Hin]].
    apply in_map_iff in Hsub as [a [Heq _]]. subst sub.
    apply in_map_iff in Hin as [rest [Heq Hrest]]. subst args.
    simpl. f_equal. apply IH. exact Hrest.
Qed.

(** Decidable comparisons on [UnitInterval], returning [bool].  Note that
    [Section ltl] above defines [true] and [false] as stream formulas, which
    shadow the constructors of [bool]; these two helpers confine the resulting
    [Datatypes.] qualification to a single place. *)
Definition ui_ltb (v w : UnitInterval) : bool :=
  if Rlt_dec (proj1_sig v) (proj1_sig w) then Datatypes.true else Datatypes.false.

Definition ui_leb (v w : UnitInterval) : bool :=
  if Rle_dec (proj1_sig v) (proj1_sig w) then Datatypes.true else Datatypes.false.

Lemma ui_ltb_spec : forall v w, ui_ltb v w = Datatypes.true <-> proj1_sig v < proj1_sig w.
Proof.
  intros v w. unfold ui_ltb. destruct (Rlt_dec (proj1_sig v) (proj1_sig w)).
  - split; intros _; [assumption | reflexivity].
  - split; intros H; [discriminate | contradiction].
Qed.

Lemma ui_leb_spec : forall v w, ui_leb v w = Datatypes.true <-> proj1_sig v <= proj1_sig w.
Proof.
  intros v w. unfold ui_leb. destruct (Rle_dec (proj1_sig v) (proj1_sig w)).
  - split; intros _; [assumption | reflexivity].
  - split; intros H; [discriminate | contradiction].
Qed.

(** Elements of [l] strictly greater than [v]. *)
Definition above (v : UnitInterval) (l : list UnitInterval) : list UnitInterval :=
  filter (fun w => ui_ltb v w) l.

Lemma above_spec : forall (v : UnitInterval) (l : list UnitInterval) (w : UnitInterval),
  In w (above v l) <-> In w l /\ proj1_sig v < proj1_sig w.
Proof.
  intros v l w. unfold above. rewrite filter_In.
  split; intros [H1 H2]; split; try assumption.
  - apply ui_ltb_spec. exact H2.
  - apply ui_ltb_spec. exact H2.
Qed.

(** Decidable equality on [UnitInterval]: the carrier is an [R] together with a
    proof, and [unitinterval_eq] disposes of the proof component. *)
Definition ui_eq_dec : forall v w : UnitInterval, {v = w} + {v <> w}.
Proof.
  intros v w. destruct (Req_EM_T (proj1_sig v) (proj1_sig w)) as [Heq | Hne].
  - left. apply unitinterval_eq. exact Heq.
  - right. intros H. apply Hne. rewrite H. reflexivity.
Defined.

Lemma ui_ltb_false : forall v w,
  ui_ltb v w = Datatypes.false <-> ~ (proj1_sig v < proj1_sig w).
Proof.
  intros v w. unfold ui_ltb. destruct (Rlt_dec (proj1_sig v) (proj1_sig w)).
  - split; intros H; [discriminate | contradiction].
  - split; intros _; [assumption | reflexivity].
Qed.

(** The least element of [l], if [l] is non-empty. *)
Fixpoint min_of (l : list UnitInterval) : option UnitInterval :=
  match l with
  | [] => None
  | x :: r =>
      match min_of r with
      | None => Some x
      | Some y => Some (if ui_ltb y x then y else x)
      end
  end.

Lemma min_of_none : forall l, min_of l = None -> l = [].
Proof.
  intros [| x r]; simpl; [reflexivity |].
  destruct (min_of r); intros H; discriminate.
Qed.

Lemma min_of_some : forall l w, min_of l = Some w ->
  In w l /\ forall u, In u l -> proj1_sig w <= proj1_sig u.
Proof.
  induction l as [| x r IH]; simpl; intros w H; [discriminate |].
  destruct (min_of r) as [y |] eqn:Hr.
  - destruct (IH y eq_refl) as [Hiny Hminy].
    destruct (ui_ltb y x) eqn:Hb; injection H as Hw; subst w.
    + apply ui_ltb_spec in Hb. split; [right; exact Hiny |].
      intros u [Hu | Hu]; [subst u; lra | apply Hminy; exact Hu].
    + apply ui_ltb_false in Hb. split; [left; reflexivity |].
      intros u [Hu | Hu]; [subst u; apply Rle_refl |].
      apply Rle_trans with (proj1_sig y); [lra | apply Hminy; exact Hu].
  - injection H as Hw; subst w. apply min_of_none in Hr. subst r.
    split; [left; reflexivity |].
    intros u [Hu | []]. subst u. apply Rle_refl.
Qed.

(** The least element of [l] strictly above [v] -- the successor of [v] in the
    finite set [l], if [v] has one there. *)
Definition min_above (v : UnitInterval) (l : list UnitInterval) : option UnitInterval :=
  min_of (above v l).

Lemma min_above_none : forall v l u,
  min_above v l = None -> In u l -> proj1_sig u <= proj1_sig v.
Proof.
  intros v l u H Hu. unfold min_above in H. apply min_of_none in H.
  apply Rnot_lt_le. intros Hlt.
  assert (In u (above v l)) as Hin by (apply above_spec; split; assumption).
  rewrite H in Hin. contradiction.
Qed.

Lemma min_above_some : forall v l w,
  min_above v l = Some w ->
  In w l /\ proj1_sig v < proj1_sig w
  /\ forall u, In u l -> proj1_sig v < proj1_sig u -> proj1_sig w <= proj1_sig u.
Proof.
  intros v l w H. unfold min_above in H. apply min_of_some in H as [Hin Hmin].
  apply above_spec in Hin as [Hinl Hlt].
  split; [exact Hinl | split; [exact Hlt |]].
  intros u Hu Hvu. apply Hmin. apply above_spec. split; assumption.
Qed.

(** ** List helpers for the size bounds *)

Lemma length_filter_le : forall {A : Type} (p : A -> bool) (l : list A),
  (length (filter p l) <= length l)%nat.
Proof.
  intros A p l. induction l as [| x xs IH]; simpl; [reflexivity |].
  destruct (p x); simpl; lia.
Qed.

Lemma in_list_sum_le : forall {A : Type} (f : A -> nat) (l : list A) (x : A),
  In x l -> (f x <= list_sum (ListDef.map f l))%nat.
Proof.
  intros A f l x. induction l as [| y ys IH]; simpl; [contradiction |].
  intros [Hy | Hy]; [subst y; lia |].
  specialize (IH Hy). lia.
Qed.

Lemma zip_apply_length_le : forall {A B : Type} (fs : list (A -> B)) (xs : list A),
  (length (zip_apply fs xs) <= length fs)%nat.
Proof.
  intros A B fs. induction fs as [| f fs' IH]; intros [| x xs']; simpl;
    try lia. specialize (IH xs'). lia.
Qed.

Lemma zip_apply_in : forall {A B : Type} (fs : list (A -> B)) (xs : list A) (y : B),
  In y (zip_apply fs xs) -> exists g, In g fs /\ exists x, In x xs /\ y = g x.
Proof.
  intros A B fs. induction fs as [| f fs' IH]; intros [| x xs'] y Hy;
    simpl in Hy; try contradiction.
  destruct Hy as [Hy | Hy].
  - exists f. split; [left; reflexivity |].
    exists x. split; [left; reflexivity | symmetry; exact Hy].
  - destruct (IH xs' y Hy) as [g [Hg [x' [Hx' Heq]]]].
    exists g. split; [right; exact Hg |].
    exists x'. split; [right; exact Hx' | exact Heq].
Qed.

Section ltl_connectives.
  Variable AP : Set.

  Definition big_or : list (ltl_expr AP) -> ltl_expr AP := fold_right (OR AP) (FALSE AP).
  Definition big_and : list (ltl_expr AP) -> ltl_expr AP := fold_right (AND AP) (TRUE AP).

  Lemma big_or_correct : forall c l,
    ltl_sat AP c (big_or l) <-> Exists (fun phi => ltl_sat AP c phi) l.
  Proof.
    intros c l. induction l as [| x xs IH]; simpl.
    - split; [contradiction | intros H; inversion H].
    - split.
      + intros [H | H]; [apply Exists_cons_hd; exact H
                        | apply Exists_cons_tl; apply IH; exact H].
      + intros H. inversion H; subst; [left; assumption | right; apply IH; assumption].
  Qed.

  Lemma big_and_correct : forall c l,
    ltl_sat AP c (big_and l) <-> Forall (fun phi => ltl_sat AP c phi) l.
  Proof.
    intros c l. induction l as [| x xs IH]; simpl.
    - split; [intros _; constructor | intros _; exact I].
    - split.
      + intros [H1 H2]. constructor; [exact H1 | apply IH; exact H2].
      + intros H. inversion H; subst. split; [assumption | apply IH; assumption].
  Qed.

  Lemma big_or_size : forall l m,
    (forall x, In x l -> (ltl_size AP x <= m)%nat) ->
    (ltl_size AP (big_or l) <= 1 + length l * (1 + m))%nat.
  Proof.
    intros l m H. induction l as [| x xs IH]; simpl; [lia |].
    assert (Hx : (ltl_size AP x <= m)%nat) by (apply H; left; reflexivity).
    assert (Hxs : (ltl_size AP (big_or xs) <= 1 + length xs * (1 + m))%nat)
      by (apply IH; intros y Hy; apply H; right; exact Hy).
    lia.
  Qed.

  Lemma big_and_size : forall l m,
    (forall x, In x l -> (ltl_size AP x <= m)%nat) ->
    (ltl_size AP (big_and l) <= 1 + length l * (1 + m))%nat.
  Proof.
    intros l m H. induction l as [| x xs IH]; simpl; [lia |].
    assert (Hx : (ltl_size AP x <= m)%nat) by (apply H; left; reflexivity).
    assert (Hxs : (ltl_size AP (big_and xs) <= 1 + length xs * (1 + m))%nat)
      by (apply IH; intros y Hy; apply H; right; exact Hy).
    lia.
  Qed.

End ltl_connectives.

(** * From [ltl_f] plus a threshold, to [ltl] *)

Section ltl_of_ltl_f.
  Variables AP F : Set.
  Variable f_to_function : F -> (list UnitInterval -> UnitInterval).

  Let sat_val := sat_val AP F f_to_function.
  Let psv := possible_statsfaction_values AP F f_to_function.

  (** The bridge lemma, and the reason the [UNTIL] case of both translations is
      cheap: thresholding [ltl_f]'s max-of-achieved-candidates semantics for
      [UNTIL] at any [v] yields exactly the classical "eventually [e2], with
      [e1] holding throughout" shape.  Both directions come straight out of
      [until_lemmas]. *)
  Lemma until_threshold : forall c e1 e2 (v : R),
    v <= proj1_sig (sat_val c (ltl_f.UNTIL AP F e1 e2))
    <-> exists i : nat,
          v <= proj1_sig (sat_val (nth_tail AP c i) e2)
       /\ forall j : nat, (j < i)%nat -> v <= proj1_sig (sat_val (nth_tail AP c j) e1).
  Proof.
    intros c e1 e2 v. split.
    - intros Hle.
      pose proof (sat_val_until_achieved AP F f_to_function c e1 e2) as Hach.
      apply (until_is_achieved_iff AP F (ltl_f.sat_val AP F f_to_function)) in Hach.
      destruct Hach as [i [H1 [_ H3]]].
      unfold until_candidate_le_e2_at_i in H1.
      unfold until_candidate_le_all_e1_before_i in H3.
      exists i. split.
      + apply (Rle_trans _ _ _ Hle H1).
      + intros j Hj. apply (Rle_trans _ _ _ Hle (H3 j Hj)).
    - intros [i [H1 H2]].
      apply (until_achieved_bound AP F f_to_function c e1 e2 i); assumption.
  Qed.

  (** ** The translation

      [ge_ltl e r] is a boolean [ltl] formula holding exactly on those
      computations where [e] scores at least [r].

      The [F_TERM] case is where the exponential blow-up lives: since [f] is an
      arbitrary function on the unit interval, the only way to decide whether it
      clears [r] is to enumerate every combination of values its arguments could
      take -- [cartesian_product] over [psv] of each argument -- keep the tuples
      on which [f] does clear [r], and assert that the arguments realise one of
      them.  "Argument [e0] takes exactly value [v]" is in turn [ge_ltl e0 v]
      together with the denial of [ge_ltl e0 w] for every larger candidate [w].

      Every recursive call sits under a [map] over the subformula list [l],
      which is the same shape [sat_val] itself uses, so this passes the guard
      checker without well-founded recursion. *)
  Fixpoint ge_ltl (e : ltl_f_expr AP F) (r : UnitInterval) : ltl_expr AP :=
    match e with
    | ltl_f.TRUE _ _      => TRUE AP
    | ltl_f.FALSE _ _     => if Rle_dec (proj1_sig r) 0 then TRUE AP else FALSE AP
    | ltl_f.AP_TERM _ _ p => if Rle_dec (proj1_sig r) 0 then TRUE AP else AP_TERM AP p
    | ltl_f.NEXT _ _ e0   => NEXT AP (ge_ltl e0 r)
    | ltl_f.UNTIL _ _ e1 e2 => UNTIL AP (ge_ltl e1 r) (ge_ltl e2 r)
    | ltl_f.F_TERM _ _ f l =>
        let tbl := ListDef.map (fun e0 => fun v => AND AP (ge_ltl e0 v) (NOT AP (big_or AP (ListDef.map (fun w => ge_ltl e0 w) (above v (psv e0)))))) l in
        big_or AP (ListDef.map (fun args => big_and AP (zip_apply tbl args)) (filter (fun args => ui_leb r (f_to_function f args)) (cartesian_product (ListDef.map psv l))))
    end.

  (** "[e] scores exactly [r]": clears [r], but clears no larger candidate.
      Correct for any [r], including one outside [psv e] (then unsatisfiable). *)
  Definition eq_ltl (e : ltl_f_expr AP F) (r : UnitInterval) : ltl_expr AP :=
    AND AP (ge_ltl e r)
           (NOT AP (big_or AP (ListDef.map (fun w => ge_ltl e w) (above r (psv e))))).

  (** ** Correctness *)

  (** Given the threshold spec for one subformula [e0], the conjunct that
      [ge_ltl] emits for it pins its value exactly.  This is the engine of both
      the [F_TERM] case below and of [eq_ltl_correct]. *)
  Lemma exactly_spec :
    forall (e0 : ltl_f_expr AP F) (c : Computation AP),
      (forall c' r', ltl_sat AP c' (ge_ltl e0 r') <-> proj1_sig r' <= proj1_sig (sat_val c' e0)) ->
      forall v : UnitInterval,
        ltl_sat AP c (AND AP (ge_ltl e0 v) (NOT AP (big_or AP (ListDef.map (fun w => ge_ltl e0 w) (above v (psv e0)))))) <-> sat_val c e0 = v.
  Proof.
    intros e0 c IH v. simpl. split.
    - intros [Hge Hnot].
      apply IH in Hge.
      apply unitinterval_eq. apply Rle_antisym; [| exact Hge].
      destruct (Rle_dec (proj1_sig (sat_val c e0)) (proj1_sig v)) as [Hle | Hgt];
        [exact Hle |].
      exfalso. apply Hnot.
      apply big_or_correct. apply Exists_exists.
      exists (ge_ltl e0 (sat_val c e0)). split.
      + apply in_map_iff. exists (sat_val c e0). split; [reflexivity |].
        apply above_spec. split.
        * apply (proof2 AP F f_to_function e0 c).
        * lra.
      + apply IH. apply Rle_refl.
    - intros Heq. split.
      + apply IH. rewrite Heq. apply Rle_refl.
      + intros Hcontra. apply big_or_correct in Hcontra.
        apply Exists_exists in Hcontra as [phi [Hin Hsat]].
        apply in_map_iff in Hin as [w [Heqphi Hinw]]. subst phi.
        apply above_spec in Hinw as [_ Hlt].
        apply IH in Hsat. rewrite Heq in Hsat. lra.
  Qed.

  (** The actual argument values of an [F_TERM] always form one of the tuples
      enumerated by [cartesian_product] -- this is [proof2], lifted pointwise. *)
  Lemma forall2_sat_val_in_psv : forall (c : Computation AP) (l : list (ltl_f_expr AP F)),
    Forall2 (fun choice lst => In choice lst)
      (ListDef.map (fun item => sat_val c item) l) (ListDef.map psv l).
  Proof.
    intros c l. induction l as [| x xs IH]; simpl; constructor.
    - apply (proof2 AP F f_to_function x c).
    - exact IH.
  Qed.

  (** Conversely: if the conjunction emitted for a tuple [args] holds, then
      [args] *is* the tuple of actual argument values. *)
  Lemma zip_apply_pins_values :
    forall (c : Computation AP) (l : list (ltl_f_expr AP F)) (args : list UnitInterval),
      (forall x, In x l ->
         forall c' r', ltl_sat AP c' (ge_ltl x r')
                       <-> proj1_sig r' <= proj1_sig (sat_val c' x)) ->
      length args = length l ->
      Forall (fun phi => ltl_sat AP c phi)
        (zip_apply
           (ListDef.map (fun e0 => fun v =>
              AND AP (ge_ltl e0 v)
                  (NOT AP (big_or AP (ListDef.map (fun w => ge_ltl e0 w)
                                        (above v (psv e0)))))) l)
           args) ->
      ListDef.map (fun item => sat_val c item) l = args.
  Proof.
    intros c l. induction l as [| x xs IHl]; intros args IHall Hlen Hforall.
    - destruct args; [reflexivity | simpl in Hlen; discriminate].
    - destruct args as [| a args']; [simpl in Hlen; discriminate |].
      simpl in Hforall. inversion Hforall as [| ? ? Hhead Htail]; subst.
      simpl. f_equal.
      + assert (Hx : forall c' r', ltl_sat AP c' (ge_ltl x r')
                                   <-> proj1_sig r' <= proj1_sig (sat_val c' x))
          by (intros c' r'; apply IHall; left; reflexivity).
        apply (exactly_spec x c Hx a). exact Hhead.
      + apply IHl.
        * intros y Hy. apply IHall. right. exact Hy.
        * simpl in Hlen. lia.
        * exact Htail.
  Qed.

  (** The threshold translation is correct: [ge_ltl e r] holds exactly where
      [e] scores at least [r]. *)
  Theorem ge_ltl_correct :
    forall (e : ltl_f_expr AP F) (c : Computation AP) (r : UnitInterval),
      ltl_sat AP c (ge_ltl e r) <-> proj1_sig r <= proj1_sig (sat_val c e).
  Proof.
    intros e.
    induction e as [ | | p | l f IH | e0 IH | e1 e2 IH ] using ltl_f_induction_principle.
    - (* TRUE : value is 1, and every threshold is at most 1 *)
      intros c r. simpl. split; intros _.
      + destruct r as [rv [Hlo Hhi]]. simpl. exact Hhi.
      + exact I.
    - (* FALSE : value is 0 *)
      intros c r. simpl. destruct (Rle_dec (proj1_sig r) 0) as [Hle | Hgt].
      + simpl. split; intros _; [exact Hle | exact I].
      + simpl. split; [intros [] | intros H; contradiction].
    - (* AP_TERM : value is 0 or 1, so above 0 the threshold degenerates *)
      intros c r. simpl. destruct (Rle_dec (proj1_sig r) 0) as [Hle | Hgt].
      + simpl. split; intros _; [| exact I].
        destruct (value_of_ap_at_time AP c p 0) as [x |].
        * destruct x as [xv Hx]. simpl in *. destruct Hx as [Hx | Hx]; lra.
        * simpl. lra.
      + simpl. destruct (value_of_ap_at_time AP c p 0) as [x |] eqn:Hv.
        * destruct (atomic_proposition_one_or_zero x) as [Hx | Hx]; subst x; simpl.
          -- split.
             ++ intros H. injection H as H. lra.
             ++ intros H. contradiction.
          -- split; intros _; [destruct r as [rv [Hlo Hhi]]; exact Hhi | reflexivity].
        * simpl. split; [intros H; discriminate | intros H; contradiction].
    - (* F_TERM : the exponential case *)
      intros c r. split.
      + intros Hsat. simpl in Hsat.
        apply big_or_correct in Hsat.
        apply Exists_exists in Hsat as [phi [Hin Hphi]].
        apply in_map_iff in Hin as [args [Heq Hinargs]]. subst phi.
        apply filter_In in Hinargs as [Hinprod Hleb].
        apply ui_leb_spec in Hleb.
        apply big_and_correct in Hphi.
        assert (Hlen : length args = length l).
        { rewrite <- (length_map psv l).
          apply (cartesian_product_length (ListDef.map psv l)). exact Hinprod. }
        assert (Hvals : ListDef.map (fun item => sat_val c item) l = args)
          by (apply (zip_apply_pins_values c l args IH Hlen Hphi)).
        simpl. rewrite Hvals. exact Hleb.
      + intros Hle. simpl. apply big_or_correct. apply Exists_exists.
        exists (big_and AP
                 (zip_apply
                    (ListDef.map (fun e0 => fun v =>
                       AND AP (ge_ltl e0 v)
                           (NOT AP (big_or AP (ListDef.map (fun w => ge_ltl e0 w)
                                                 (above v (psv e0)))))) l)
                    (ListDef.map (fun item => sat_val c item) l))).
        split.
        * apply in_map_iff.
          exists (ListDef.map (fun item => sat_val c item) l).
          split; [reflexivity |].
          apply filter_In. split.
          -- apply cartesian_product_correct. apply forall2_sat_val_in_psv.
          -- apply ui_leb_spec. simpl in Hle. exact Hle.
        * apply big_and_correct. rewrite zip_apply_map_map.
          apply Forall_forall. intros phi Hin.
          apply in_map_iff in Hin as [e0 [Heq Hine0]]. subst phi.
          apply (exactly_spec e0 c (IH e0 Hine0)). reflexivity.
    - (* NEXT *)
      intros c r. simpl. apply IH.
    - (* UNTIL : the whole case is [until_threshold] plus the two IHs *)
      intros c r. destruct IH as [IH1 IH2].
      rewrite until_threshold. cbn [ltl_sat].
      split.
      + intros [i [H2 H1]]. exists i. split.
        * apply IH2. exact H2.
        * intros j Hj. apply IH1. apply H1. exact Hj.
      + intros [i [H2 H1]]. exists i. split.
        * apply IH2. exact H2.
        * intros j Hj. apply IH1. apply H1. exact Hj.
  Qed.

  (** The headline statement: [e] scores exactly [r] on [c] precisely when the
      compiled boolean formula holds on [c]. *)
  Theorem eq_ltl_correct :
    forall (e : ltl_f_expr AP F) (c : Computation AP) (r : UnitInterval),
      ltl_sat AP c (eq_ltl e r) <-> sat_val c e = r.
  Proof.
    intros e c r. unfold eq_ltl.
    apply (exactly_spec e c). intros c' r'. apply ge_ltl_correct.
  Qed.

  (** ** Membership in a set of values

      The interface the rest of the development wants is not a threshold but a
      set: given a list [P] of candidate values, a boolean [ltl] formula that
      holds exactly when [sat_val c e] is one of them.

      [eq_ltl] above answers this for a one-element [P], but at the cost of one
      [ge_ltl] copy per larger candidate in [psv e].  That is wasteful: since
      [sat_val c e] always lies in [psv e] ([proof2]), "[e] scores exactly [v]"
      only has to exclude the *next* candidate above [v], not all of them.
      [min_above] supplies it, so each value costs two copies of [ge_ltl] and a
      whole set costs two per element -- no worse, for any [P] no longer than
      [psv e], than the old single-value formula. *)

  (** [a <= sat_val c e], and [sat_val c e < u] when an upper bound [Some u] is
      given.  Both [exact_ltl] and any union-of-intervals refinement are built
      from this. *)
  Definition range_ltl (e : ltl_f_expr AP F) (a : UnitInterval)
                       (w : option UnitInterval) : ltl_expr AP :=
    match w with
    | None => ge_ltl e a
    | Some u => AND AP (ge_ltl e a) (NOT AP (ge_ltl e u))
    end.

  Lemma range_ltl_correct : forall e c a w,
    ltl_sat AP c (range_ltl e a w)
    <-> proj1_sig a <= proj1_sig (sat_val c e)
        /\ forall u, w = Some u -> proj1_sig (sat_val c e) < proj1_sig u.
  Proof.
    intros e c a [u |]; simpl.
    - rewrite !ge_ltl_correct. split.
      + intros [Ha Hu]. split; [exact Ha |].
        intros u' Heq. injection Heq as Hu'; subst u'. lra.
      + intros [Ha Hu]. split; [exact Ha |].
        intros Hcontra. specialize (Hu u eq_refl). lra.
    - rewrite ge_ltl_correct. split.
      + intros Ha. split; [exact Ha | intros u Heq; discriminate].
      + intros [Ha _]. exact Ha.
  Qed.

  (** "[e] scores exactly [v]": clears [v], but not [v]'s successor in [psv e]. *)
  Definition exact_ltl (e : ltl_f_expr AP F) (v : UnitInterval) : ltl_expr AP :=
    range_ltl e v (min_above v (psv e)).

  Lemma exact_ltl_correct : forall e c v,
    ltl_sat AP c (exact_ltl e v) <-> sat_val c e = v.
  Proof.
    intros e c v. unfold exact_ltl. rewrite range_ltl_correct.
    assert (Hin : In (sat_val c e) (psv e)) by apply (proof2 AP F f_to_function e c).
    destruct (min_above v (psv e)) as [w |] eqn:Hma.
    - destruct (min_above_some v (psv e) w Hma) as [_ [Hvw Hmin]].
      split.
      + intros [Hge Hlt]. specialize (Hlt w eq_refl).
        apply unitinterval_eq. apply Rle_antisym; [| exact Hge].
        apply Rnot_lt_le. intros Hgt. specialize (Hmin _ Hin Hgt). lra.
      + intros Heq. rewrite Heq. split; [apply Rle_refl |].
        intros u Hu. injection Hu as Hu'; subst u. exact Hvw.
    - split.
      + intros [Hge _]. apply unitinterval_eq. apply Rle_antisym; [| exact Hge].
        apply (min_above_none v (psv e) _ Hma Hin).
      + intros Heq. rewrite Heq. split; [apply Rle_refl | intros u Hu; discriminate].
  Qed.

  (** The same statement [eq_ltl_correct] makes, for a formula with two copies
      of [ge_ltl] instead of [1 + length (above r (psv e))] of them. *)
  Corollary exact_ltl_eq_ltl : forall e c r,
    ltl_sat AP c (exact_ltl e r) <-> ltl_sat AP c (eq_ltl e r).
  Proof.
    intros e c r. rewrite exact_ltl_correct, eq_ltl_correct. tauto.
  Qed.

  (** ** The set version

      [in_ltl e P] holds exactly on the computations where [e]'s score is one
      of the values listed in [P]. *)
  Definition in_ltl (e : ltl_f_expr AP F) (P : list UnitInterval) : ltl_expr AP :=
    big_or AP (ListDef.map (fun v => exact_ltl e v) P).

  Theorem in_ltl_correct : forall (e : ltl_f_expr AP F) (c : Computation AP)
                                  (P : list UnitInterval),
    ltl_sat AP c (in_ltl e P) <-> In (sat_val c e) P.
  Proof.
    intros e c P. unfold in_ltl. rewrite big_or_correct, Exists_exists. split.
    - intros [phi [Hin Hsat]]. apply in_map_iff in Hin as [v [Hphi Hv]].
      subst phi. apply exact_ltl_correct in Hsat. rewrite Hsat. exact Hv.
    - intros Hin. exists (exact_ltl e (sat_val c e)). split.
      + apply in_map_iff. exists (sat_val c e). split; [reflexivity | exact Hin].
      + apply exact_ltl_correct. reflexivity.
  Qed.

  Corollary in_ltl_singleton : forall e c r,
    ltl_sat AP c (in_ltl e [r]) <-> sat_val c e = r.
  Proof.
    intros e c r. rewrite in_ltl_correct. simpl. split.
    - intros [H | []]. symmetry. exact H.
    - intros H. left. symmetry. exact H.
  Qed.

  (** ** Trimming [P]

      Values outside [psv e] are unreachable and duplicates are redundant, so
      [P] may be cut down before compiling.  This changes nothing semantically
      and caps the number of disjuncts at [length (psv e)] however long [P]
      was -- the formula's size is therefore controlled by [e] alone. *)
  Definition trim (e : ltl_f_expr AP F) (P : list UnitInterval) : list UnitInterval :=
    nodup ui_eq_dec
      (filter (fun v => if in_dec ui_eq_dec v (psv e)
                        then Datatypes.true else Datatypes.false) P).

  Lemma trim_spec : forall e c P,
    In (sat_val c e) (trim e P) <-> In (sat_val c e) P.
  Proof.
    intros e c P. unfold trim. rewrite nodup_In, filter_In. split.
    - intros [H _]. exact H.
    - intros H. split; [exact H |].
      destruct (in_dec ui_eq_dec (sat_val c e) (psv e)) as [_ | Hno];
        [reflexivity | exfalso; apply Hno; apply (proof2 AP F f_to_function e c)].
  Qed.

  Lemma trim_length : forall e P, (length (trim e P) <= length (psv e))%nat.
  Proof.
    intros e P. apply NoDup_incl_length; [apply NoDup_nodup |].
    intros v Hv. unfold trim in Hv. rewrite nodup_In, filter_In in Hv.
    destruct Hv as [_ Hdec].
    destruct (in_dec ui_eq_dec v (psv e)); [assumption | discriminate].
  Qed.

  Theorem in_ltl_trim_correct : forall e c P,
    ltl_sat AP c (in_ltl e (trim e P)) <-> In (sat_val c e) P.
  Proof. intros e c P. rewrite in_ltl_correct. apply trim_spec. Qed.

  (** ** How long is the compiled formula?

      [ge_ltl e r]'s size barely depends on [r]: [r] only picks between [TRUE]
      and [FALSE] at the leaves, and prunes the [filter] in the [F_TERM] case,
      which can only shrink the result.  [ge_bound e] is the resulting [r]-free
      bound, and it is where the blow-up is visible -- the [F_TERM] case
      multiplies by [length (cartesian_product (map psv l))], the product over
      the arguments of how many values each of them can take. *)
  Fixpoint ge_bound (e : ltl_f_expr AP F) : nat :=
    match e with
    | ltl_f.TRUE _ _        => 1
    | ltl_f.FALSE _ _       => 1
    | ltl_f.AP_TERM _ _ _   => 1
    | ltl_f.NEXT _ _ e0     => 1 + ge_bound e0
    | ltl_f.UNTIL _ _ e1 e2 => 1 + ge_bound e1 + ge_bound e2
    | ltl_f.F_TERM _ _ f l =>
        1 + length (cartesian_product (ListDef.map psv l))
            * (2 + length l
                   * (1 + list_sum (ListDef.map
                        (fun e0 => (3 + ge_bound e0
                                     + length (psv e0) * (1 + ge_bound e0))%nat) l)))
    end.

  (** One entry of the [F_TERM] table -- "argument [e0] takes exactly [v]". *)
  Lemma tbl_entry_size : forall e0 v,
    (forall r, (ltl_size AP (ge_ltl e0 r) <= ge_bound e0)%nat) ->
    (ltl_size AP (AND AP (ge_ltl e0 v)
       (NOT AP (big_or AP (ListDef.map (fun w => ge_ltl e0 w) (above v (psv e0))))))
     <= 3 + ge_bound e0 + length (psv e0) * (1 + ge_bound e0))%nat.
  Proof.
    intros e0 v IH.
    assert (Hb : (ltl_size AP (big_or AP (ListDef.map (fun w => ge_ltl e0 w)
                                            (above v (psv e0))))
                  <= 1 + length (ListDef.map (fun w => ge_ltl e0 w) (above v (psv e0)))
                          * (1 + ge_bound e0))%nat).
    { apply big_or_size. intros x Hx. apply in_map_iff in Hx as [w [Hw _]].
      subst x. apply IH. }
    rewrite length_map in Hb.
    assert (Hl : (length (above v (psv e0)) * (1 + ge_bound e0)
                  <= length (psv e0) * (1 + ge_bound e0))%nat).
    { apply Nat.mul_le_mono_r. unfold above. apply length_filter_le. }
    specialize (IH v). cbn [ltl_size]. lia.
  Qed.

  (** The [F_TERM] case of the bound, isolated from the induction. *)
  Lemma f_term_size_le : forall (f : F) (l : list (ltl_f_expr AP F)) (r : UnitInterval),
    (forall e0, In e0 l -> forall r', (ltl_size AP (ge_ltl e0 r') <= ge_bound e0)%nat) ->
    (ltl_size AP (ge_ltl (ltl_f.F_TERM AP F f l) r)
     <= ge_bound (ltl_f.F_TERM AP F f l))%nat.
  Proof.
    intros f l r IH. cbn [ge_ltl ge_bound].
    set (tbl := ListDef.map
                  (fun e0 => fun v =>
                     AND AP (ge_ltl e0 v)
                         (NOT AP (big_or AP (ListDef.map (fun w => ge_ltl e0 w)
                                               (above v (psv e0)))))) l).
    set (M := list_sum (ListDef.map
                (fun e0 => (3 + ge_bound e0 + length (psv e0) * (1 + ge_bound e0))%nat) l)).
    assert (Hconj : forall args,
      (ltl_size AP (big_and AP (zip_apply tbl args)) <= 1 + length l * (1 + M))%nat).
    { intros args.
      apply Nat.le_trans with (m := (1 + length (zip_apply tbl args) * (1 + M))%nat).
      - apply big_and_size. intros y Hy.
        apply zip_apply_in in Hy as [g [Hg [v [_ Hy]]]]. subst y.
        unfold tbl in Hg. apply in_map_iff in Hg as [e0 [Hg Hin]]. subst g.
        apply Nat.le_trans with
          (m := (3 + ge_bound e0 + length (psv e0) * (1 + ge_bound e0))%nat).
        + apply tbl_entry_size. intros r'. apply IH. exact Hin.
        + unfold M.
          apply (in_list_sum_le
                   (fun e1 => (3 + ge_bound e1
                                 + length (psv e1) * (1 + ge_bound e1))%nat) l e0 Hin).
      - apply Nat.add_le_mono_l, Nat.mul_le_mono_r.
        apply Nat.le_trans with (m := length tbl); [apply zip_apply_length_le |].
        unfold tbl. rewrite length_map. reflexivity. }
    apply Nat.le_trans with
      (m := (1 + length (ListDef.map (fun args => big_and AP (zip_apply tbl args))
                (filter (fun args => ui_leb r (f_to_function f args))
                   (cartesian_product (ListDef.map psv l))))
             * (1 + (1 + length l * (1 + M))))%nat).
    - apply big_or_size. intros x Hx. apply in_map_iff in Hx as [args [Hargs _]].
      subst x. apply Hconj.
    - rewrite length_map.
      apply Nat.add_le_mono_l, Nat.mul_le_mono_r, length_filter_le.
  Qed.

  (** The size bound for the threshold translation, uniform in [r]. *)
  Theorem ge_ltl_size_le : forall (e : ltl_f_expr AP F) (r : UnitInterval),
    (ltl_size AP (ge_ltl e r) <= ge_bound e)%nat.
  Proof.
    intros e.
    induction e as [ | | p | l f IH | e0 IH | e1 e2 IH ] using ltl_f_induction_principle.
    - intros r. cbn. lia.
    - intros r. cbn [ge_ltl ge_bound].
      destruct (Rle_dec (proj1_sig r) 0); cbn [ltl_size]; lia.
    - intros r. cbn [ge_ltl ge_bound].
      destruct (Rle_dec (proj1_sig r) 0); cbn [ltl_size]; lia.
    - intros r. apply f_term_size_le. exact IH.
    - intros r. cbn [ge_ltl ge_bound ltl_size]. specialize (IH r). lia.
    - intros r. destruct IH as [IH1 IH2]. cbn [ge_ltl ge_bound ltl_size].
      specialize (IH1 r). specialize (IH2 r). lia.
  Qed.

  (** Two copies of [ge_ltl], as promised. *)
  Lemma exact_ltl_size_le : forall e v,
    (ltl_size AP (exact_ltl e v) <= 2 + 2 * ge_bound e)%nat.
  Proof.
    intros e v. unfold exact_ltl, range_ltl.
    pose proof (ge_ltl_size_le e v) as Hv.
    destruct (min_above v (psv e)) as [u |].
    - pose proof (ge_ltl_size_le e u) as Hu. cbn [ltl_size]. lia.
    - lia.
  Qed.

  (** The headline size bound: the set formula grows linearly in [length P],
      with the whole of the [F_TERM] blow-up confined to [ge_bound e]. *)
  Theorem in_ltl_size_le : forall e P,
    (ltl_size AP (in_ltl e P) <= 1 + length P * (3 + 2 * ge_bound e))%nat.
  Proof.
    intros e P. unfold in_ltl.
    apply Nat.le_trans with
      (m := (1 + length (ListDef.map (fun v => exact_ltl e v) P)
             * (1 + (2 + 2 * ge_bound e)))%nat).
    - apply big_or_size. intros x Hx. apply in_map_iff in Hx as [v [Hv _]].
      subst x. apply exact_ltl_size_le.
    - rewrite length_map. reflexivity.
  Qed.

  (** After trimming, the bound no longer mentions [P] at all: asking about an
      arbitrary set of values costs no more than asking about every value [e]
      can take. *)
  Theorem in_ltl_trim_size_le : forall e P,
    (ltl_size AP (in_ltl e (trim e P))
     <= 1 + length (psv e) * (3 + 2 * ge_bound e))%nat.
  Proof.
    intros e P. eapply Nat.le_trans; [apply in_ltl_size_le |].
    apply Nat.add_le_mono_l, Nat.mul_le_mono_r, trim_length.
  Qed.

End ltl_of_ltl_f.

(** * From [ltl] to [ltl_f]

    The easy direction: [ltl] embeds into [ltl_f], provided [F] supplies the
    three boolean connectives.  We ask for the standard fuzzy readings -- min,
    max and [1 - x] -- which restrict to the boolean ones on [{0, 1}]. *)

Section ltl_f_of_ltl.
  Variables AP F : Set.
  Variable f_to_function : F -> (list UnitInterval -> UnitInterval).
  Variables f_and f_or f_not : F.

  Hypothesis Hand : forall x y, f_to_function f_and [x; y] = unitinterval_min x y.
  Hypothesis Hor  : forall x y, f_to_function f_or  [x; y] = unitinterval_max x y.
  Hypothesis Hnot : forall x,   f_to_function f_not [x]    = unitinterval_comp x.

  (* A notation rather than a [Let]: this section rewrites with [until_threshold],
     whose goals mention [ltl_f.sat_val] applied outright, and a [Let]-bound
     abbreviation would not match them syntactically. *)
  Local Notation sat_val := (ltl_f.sat_val AP F f_to_function).

  Fixpoint ltl_to_ltl_f (e : ltl_expr AP) : ltl_f_expr AP F :=
    match e with
    | TRUE _        => ltl_f.TRUE AP F
    | FALSE _       => ltl_f.FALSE AP F
    | AP_TERM _ p   => ltl_f.AP_TERM AP F p
    | AND _ e1 e2   => ltl_f.F_TERM AP F f_and [ltl_to_ltl_f e1; ltl_to_ltl_f e2]
    | OR _ e1 e2    => ltl_f.F_TERM AP F f_or  [ltl_to_ltl_f e1; ltl_to_ltl_f e2]
    | NOT _ e'      => ltl_f.F_TERM AP F f_not [ltl_to_ltl_f e']
    | NEXT _ e'     => ltl_f.NEXT AP F (ltl_to_ltl_f e')
    | UNTIL _ e1 e2 => ltl_f.UNTIL AP F (ltl_to_ltl_f e1) (ltl_to_ltl_f e2)
    end.

  (** Both halves at once: the image of an [ltl] formula is two-valued, and
      takes value [one] exactly where the formula holds.  Proving them together
      avoids a separate "the image only ever scores 0 or 1" induction. *)
  Lemma ltl_to_ltl_f_two_valued : forall (e : ltl_expr AP) (c : Computation AP),
    (  ltl_sat AP c e -> sat_val c (ltl_to_ltl_f e) = one)
 /\ (~ ltl_sat AP c e -> sat_val c (ltl_to_ltl_f e) = zero).
  Proof.
    intros e.
    induction e as [ | | p | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2
                   | e' IHe' | e' IHe' | e1 IHe1 e2 IHe2 ]; intros c.
    - (* TRUE *)
      split; [intros _; reflexivity | intros H; exfalso; apply H; exact I].
    - (* FALSE *)
      split; [intros [] | intros _; reflexivity].
    - (* AP_TERM *)
      simpl. split.
      + intros H. rewrite H. apply unitinterval_eq. reflexivity.
      + intros H. destruct (value_of_ap_at_time AP c p 0) as [x |] eqn:Hv.
        * destruct (atomic_proposition_one_or_zero x) as [Hx | Hx]; subst x.
          -- apply unitinterval_eq. reflexivity.
          -- exfalso. apply H. reflexivity.
        * reflexivity.
    - (* AND *)
      simpl. rewrite Hand. split.
      + intros [H1 H2].
        rewrite (proj1 (IHe1 c) H1), (proj1 (IHe2 c) H2).
        apply ui_min_is_l. apply Rle_refl.
      + intros H. apply not_and_or in H. destruct H as [H | H].
        * rewrite (proj2 (IHe1 c) H). apply ui_min_is_l.
          destruct (proj2_sig (sat_val c (ltl_to_ltl_f e2))) as [Hlo _]. exact Hlo.
        * rewrite (proj2 (IHe2 c) H). apply ui_min_is_r.
          destruct (proj2_sig (sat_val c (ltl_to_ltl_f e1))) as [Hlo _]. exact Hlo.
    - (* OR *)
      simpl. rewrite Hor. split.
      + intros [H | H].
        * rewrite (proj1 (IHe1 c) H). apply ui_max_is_l.
          destruct (proj2_sig (sat_val c (ltl_to_ltl_f e2))) as [_ Hhi]. exact Hhi.
        * rewrite (proj1 (IHe2 c) H). apply ui_max_is_r.
          destruct (proj2_sig (sat_val c (ltl_to_ltl_f e1))) as [_ Hhi]. exact Hhi.
      + intros H. apply not_or_and in H. destruct H as [H1 H2].
        rewrite (proj2 (IHe1 c) H1), (proj2 (IHe2 c) H2).
        apply ui_max_is_l. apply Rle_refl.
    - (* NOT *)
      simpl. rewrite Hnot. split.
      + intros H. rewrite (proj2 (IHe' c) H).
        apply unitinterval_eq. simpl. lra.
      + intros H. apply NNPP in H. rewrite (proj1 (IHe' c) H).
        apply unitinterval_eq. simpl. lra.
    - (* NEXT *)
      simpl. apply IHe'.
    - (* UNTIL *)
      (* Two facts about each subformula, extracted from its IH by [classic]:
         its value is 0 or 1, and value 1 forces satisfaction. *)
      assert (Hbin : forall (e : ltl_expr AP) (c' : Computation AP),
                (forall c'', (ltl_sat AP c'' e -> sat_val c'' (ltl_to_ltl_f e) = one)
                          /\ (~ ltl_sat AP c'' e -> sat_val c'' (ltl_to_ltl_f e) = zero)) ->
                proj1_sig (sat_val c' (ltl_to_ltl_f e)) = 0
                \/ proj1_sig (sat_val c' (ltl_to_ltl_f e)) = 1).
      { intros e c' IHe. destruct (classic (ltl_sat AP c' e)) as [Hy | Hn].
        - right. rewrite (proj1 (IHe c') Hy). reflexivity.
        - left. rewrite (proj2 (IHe c') Hn). reflexivity. }
      assert (Hone : forall (e : ltl_expr AP) (c' : Computation AP),
                (forall c'', (ltl_sat AP c'' e -> sat_val c'' (ltl_to_ltl_f e) = one)
                          /\ (~ ltl_sat AP c'' e -> sat_val c'' (ltl_to_ltl_f e) = zero)) ->
                proj1_sig (sat_val c' (ltl_to_ltl_f e)) = 1 -> ltl_sat AP c' e).
      { intros e c' IHe Hv. destruct (classic (ltl_sat AP c' e)) as [Hy | Hn];
          [exact Hy |].
        exfalso. rewrite (proj2 (IHe c') Hn) in Hv. simpl in Hv. lra. }
      split.
      + (* satisfied: the witness gives value 1 all along, so the max is 1 *)
        intros [i [H2 H1]]. apply unitinterval_eq.
        destruct (proj2_sig (sat_val c (ltl_to_ltl_f (UNTIL AP e1 e2)))) as [_ Hhi].
        simpl in Hhi |- *. apply Rle_antisym; [exact Hhi |].
        apply until_threshold. exists i. split.
        * rewrite (proj1 (IHe2 (nth_tail AP c i)) H2). apply Rle_refl.
        * intros j Hj. rewrite (proj1 (IHe1 (nth_tail AP c j)) (H1 j Hj)). apply Rle_refl.
      + (* unsatisfied: any positive value would reconstruct a witness *)
        intros Hno. apply unitinterval_eq.
        destruct (proj2_sig (sat_val c (ltl_to_ltl_f (UNTIL AP e1 e2)))) as [Hlo _].
        simpl in Hlo |- *. apply Rle_antisym; [| exact Hlo].
        destruct (Rle_dec (proj1_sig (sat_val c (ltl_f.UNTIL AP F (ltl_to_ltl_f e1)
                                                                 (ltl_to_ltl_f e2)))) 0)
          as [Hle | Hgt]; [exact Hle |].
        exfalso. apply Rnot_le_lt in Hgt.
        assert (Hth : proj1_sig (sat_val c (ltl_f.UNTIL AP F (ltl_to_ltl_f e1)
                                                             (ltl_to_ltl_f e2)))
                      <= proj1_sig (sat_val c (ltl_f.UNTIL AP F (ltl_to_ltl_f e1)
                                                                (ltl_to_ltl_f e2))))
          by apply Rle_refl.
        apply until_threshold in Hth. destruct Hth as [i [H2 H1]].
        apply Hno. exists i. split.
        * apply (Hone e2 (nth_tail AP c i) IHe2).
          destruct (Hbin e2 (nth_tail AP c i) IHe2) as [Hz | Ho]; [lra | exact Ho].
        * intros j Hj. apply (Hone e1 (nth_tail AP c j) IHe1).
          destruct (Hbin e1 (nth_tail AP c j) IHe1) as [Hz | Ho];
            [specialize (H1 j Hj); lra | exact Ho].
  Qed.

  (** [ltl] is faithfully embedded in [ltl_f]: satisfaction on the [ltl] side
      corresponds to scoring the top value [one] on the [ltl_f] side. *)
  Theorem ltl_to_ltl_f_correct : forall (e : ltl_expr AP) (c : Computation AP),
    ltl_sat AP c e <-> sat_val c (ltl_to_ltl_f e) = one.
  Proof.
    intros e c. split.
    - apply (ltl_to_ltl_f_two_valued e c).
    - intros Hone. destruct (classic (ltl_sat AP c e)) as [Hy | Hn]; [exact Hy |].
      exfalso.
      rewrite (proj2 (ltl_to_ltl_f_two_valued e c) Hn) in Hone.
      assert (proj1_sig zero = proj1_sig one) as Hcontra by (rewrite Hone; reflexivity).
      simpl in Hcontra. lra.
  Qed.

  (** Both translations composed: pushing an [ltl] formula into [ltl_f] and
      compiling it back at threshold [one] recovers exactly the original
      formula's meaning.  [ltl] is thus a retract of [ltl_f], which is the
      precise sense in which the two logics are equally expressive despite
      [ltl_f] being the strictly larger syntax. *)
  Theorem ltl_round_trip : forall (e : ltl_expr AP) (c : Computation AP),
    ltl_sat AP c e <-> ltl_sat AP c (ge_ltl AP F f_to_function (ltl_to_ltl_f e) one).
  Proof.
    intros e c. rewrite ge_ltl_correct. rewrite ltl_to_ltl_f_correct.
    split.
    - intros H. rewrite H. apply Rle_refl.
    - intros H. apply unitinterval_eq.
      destruct (proj2_sig (sat_val c (ltl_to_ltl_f e))) as [_ Hhi].
      simpl in *. apply Rle_antisym; assumption.
  Qed.

  Theorem ltl_round_trip_exact : forall (e : ltl_expr AP) (c : Computation AP),
    ltl_sat AP c e <-> ltl_sat AP c (eq_ltl AP F f_to_function (ltl_to_ltl_f e) one).
  Proof.
    intros e c. rewrite (eq_ltl_correct AP F f_to_function).
    apply ltl_to_ltl_f_correct.
  Qed.

End ltl_f_of_ltl.

From LTL_F_Project Require Import bounds.

(** * A closed-form bound on the length of the compiled formula

    [ge_bound] is exact enough to be useful but is itself a recursion over the
    formula.  Folding in [bounds.v]'s [possible_statsfaction_values_bounded]
    turns it into a closed form: the compiled [ltl] formula is at most
    [2 ^ (5 * n ^ 2)] nodes long, where [n] is the size of the [ltl_f] formula.
    That is the precise sense of "at most exponentially longer". *)

(** ** Arithmetic helpers *)

Lemma pow2_ge_1 : forall k : nat, (1 <= 2 ^ k)%nat.
Proof. intros k. apply Nat.neq_0_lt_0, Nat.pow_nonzero. lia. Qed.

Lemma pow2_mono : forall j k : nat, (j <= k)%nat -> (2 ^ j <= 2 ^ k)%nat.
Proof. intros j k H. apply Nat.pow_le_mono_r; [lia | exact H]. Qed.

Lemma pow2_le_mono : forall a j k : nat,
  (a <= 2 ^ j)%nat -> (j <= k)%nat -> (a <= 2 ^ k)%nat.
Proof.
  intros a j k Ha Hjk. apply Nat.le_trans with (m := (2 ^ j)%nat);
    [exact Ha | apply pow2_mono; exact Hjk].
Qed.

Lemma pow2_add_le : forall a b j : nat,
  (a <= 2 ^ j)%nat -> (b <= 2 ^ j)%nat -> (a + b <= 2 ^ (j + 1))%nat.
Proof. intros a b j Ha Hb. rewrite Nat.pow_add_r, Nat.pow_1_r. lia. Qed.

Lemma pow2_mul_le : forall a b j k : nat,
  (a <= 2 ^ j)%nat -> (b <= 2 ^ k)%nat -> (a * b <= 2 ^ (j + k))%nat.
Proof.
  intros a b j k Ha Hb. rewrite Nat.pow_add_r. apply Nat.mul_le_mono; assumption.
Qed.

Lemma n_le_pow2 : forall n : nat, (n <= 2 ^ n)%nat.
Proof.
  induction n as [| n IH]; simpl; [lia |]. pose proof (pow2_ge_1 n). lia.
Qed.

Lemma list_sum_le_length_mul : forall {A : Type} (f : A -> nat) (l : list A) (m : nat),
  (forall x, In x l -> (f x <= m)%nat) ->
  (list_sum (ListDef.map f l) <= length l * m)%nat.
Proof.
  intros A f l m H. induction l as [| x xs IH]; simpl; [lia |].
  assert (Hx : (f x <= m)%nat) by (apply H; left; reflexivity).
  assert (Hxs : (list_sum (ListDef.map f xs) <= length xs * m)%nat)
    by (apply IH; intros y Hy; apply H; right; exact Hy).
  lia.
Qed.

Section closed_size_bound.
  Variables AP F : Set.
  Variable f_to_function : F -> (list UnitInterval -> UnitInterval).

  Local Notation sz := (expr_size AP F).
  Local Notation psv := (possible_statsfaction_values AP F f_to_function).
  Local Notation bnd := (ge_bound AP F f_to_function).

  Lemma expr_size_ge_1 : forall e : ltl_f_expr AP F, (1 <= sz e)%nat.
  Proof.
    intros e.
    induction e as [ | | p | l f IH | e0 IH | e1 e2 IH ] using ltl_f_induction_principle;
      cbn [expr_size]; lia.
  Qed.

  Lemma ge_bound_ge_1 : forall e : ltl_f_expr AP F, (1 <= bnd e)%nat.
  Proof.
    intros e.
    induction e as [ | | p | l f IH | e0 IH | e1 e2 IH ] using ltl_f_induction_principle;
      cbn [ge_bound]; lia.
  Qed.

  Lemma length_le_sum_sizes : forall l : list (ltl_f_expr AP F),
    (length l <= sum_list_elements_nat (ListDef.map sz l))%nat.
  Proof.
    intros l. induction l as [| x xs IH]; cbn [length ListDef.map sum_list_elements_nat];
      [lia |]. pose proof (expr_size_ge_1 x). lia.
  Qed.

  Lemma in_le_sum_sizes : forall (l : list (ltl_f_expr AP F)) (x : ltl_f_expr AP F),
    In x l -> (sz x <= sum_list_elements_nat (ListDef.map sz l))%nat.
  Proof.
    intros l. induction l as [| y ys IH]; cbn [In ListDef.map sum_list_elements_nat];
      intros x Hx; [contradiction |].
    destruct Hx as [Heq | Hin]; [subst y; lia |]. specialize (IH x Hin). lia.
  Qed.

  (** The [F_TERM] case, where every factor of the blow-up appears at once. *)
  Lemma f_term_bound_exponential : forall (f : F) (l : list (ltl_f_expr AP F)),
    (1 <= sum_list_elements_nat (ListDef.map sz l))%nat ->
    (forall x, In x l -> (bnd x <= 2 ^ (5 * sz x * sz x))%nat) ->
    (bnd (ltl_f.F_TERM AP F f l)
     <= 2 ^ (5 * sz (ltl_f.F_TERM AP F f l) * sz (ltl_f.F_TERM AP F f l)))%nat.
  Proof.
    intros f l HS IH. cbn [ge_bound expr_size].
    set (S := sum_list_elements_nat (ListDef.map sz l)) in *.
    match goal with |- context [list_sum ?X] => set (M := list_sum X) end.
    match goal with
    | |- context [length (cartesian_product ?X)] => set (C := length (cartesian_product X))
    end.
    (* the number of tuples: [psv] of the whole [F_TERM] has exactly this length *)
    assert (HC : (C <= 2 ^ (1 + S))%nat).
    { pose proof (possible_statsfaction_values_bounded AP F f_to_function
                    (ltl_f.F_TERM AP F f l)) as H.
      cbn [possible_statsfaction_values expr_size] in H.
      rewrite length_possible_values_from_possible_args in H. exact H. }
    (* the number of arguments *)
    assert (HL : (length l <= 2 ^ (1 + S))%nat).
    { apply pow2_le_mono with (j := S); [| lia].
      apply Nat.le_trans with (m := S); [apply length_le_sum_sizes | apply n_le_pow2]. }
    (* one conjunct: "argument [x] takes exactly this value" *)
    assert (Hconj : forall x, In x l ->
      ((3 + bnd x + length (psv x) * (1 + bnd x)) <= 2 ^ (5 * S * S + S + 3))%nat).
    { intros x Hin.
      assert (Hp : (length (psv x) <= 2 ^ sz x)%nat)
        by apply possible_statsfaction_values_bounded.
      assert (Hb : (bnd x <= 2 ^ (5 * sz x * sz x))%nat) by (apply IH; exact Hin).
      assert (Hb1 : (1 <= bnd x)%nat) by apply ge_bound_ge_1.
      assert (H1p : (1 + length (psv x) <= 2 ^ (sz x + 1))%nat)
        by (apply pow2_add_le; [apply pow2_ge_1 | exact Hp]).
      assert (Hmul : (bnd x * (1 + length (psv x))
                      <= 2 ^ (5 * sz x * sz x + (sz x + 1)))%nat)
        by (apply pow2_mul_le; assumption).
      assert (H4 : (4 * (bnd x * (1 + length (psv x)))
                    <= 2 ^ (2 + (5 * sz x * sz x + (sz x + 1))))%nat)
        by (apply pow2_mul_le; [cbn; lia | exact Hmul]).
      assert (Hstep : (3 + bnd x + length (psv x) * (1 + bnd x)
                       <= 4 * (bnd x * (1 + length (psv x))))%nat) by nia.
      apply pow2_le_mono with (j := (2 + (5 * sz x * sz x + (sz x + 1)))%nat); [lia |].
      pose proof (in_le_sum_sizes l x Hin). nia. }
    assert (HM : (M <= 2 ^ (1 + S + (5 * S * S + S + 3)))%nat).
    { apply Nat.le_trans with (m := (length l * 2 ^ (5 * S * S + S + 3))%nat).
      - apply list_sum_le_length_mul. exact Hconj.
      - apply pow2_mul_le; [exact HL | apply Nat.le_refl]. }
    assert (A1 : (1 + M <= 2 ^ (1 + S + (5 * S * S + S + 3) + 1))%nat)
      by (apply pow2_add_le; [apply pow2_ge_1 | exact HM]).
    assert (A2 : (length l * (1 + M)
                  <= 2 ^ (1 + S + (1 + S + (5 * S * S + S + 3) + 1)))%nat)
      by (apply pow2_mul_le; [exact HL | exact A1]).
    assert (A3 : (2 + length l * (1 + M)
                  <= 2 ^ (1 + S + (1 + S + (5 * S * S + S + 3) + 1) + 1))%nat).
    { apply pow2_add_le; [| exact A2].
      apply pow2_le_mono with (j := 1%nat); [cbn; lia | lia]. }
    assert (A4 : (C * (2 + length l * (1 + M))
                  <= 2 ^ (1 + S + (1 + S + (1 + S + (5 * S * S + S + 3) + 1) + 1)))%nat)
      by (apply pow2_mul_le; [exact HC | exact A3]).
    apply pow2_le_mono with
      (j := (1 + S + (1 + S + (1 + S + (5 * S * S + S + 3) + 1) + 1) + 1)%nat).
    - apply pow2_add_le; [apply pow2_ge_1 | exact A4].
    - nia.
  Qed.

  (** [ge_bound] in closed form. *)
  Theorem ge_bound_exponential : forall e : ltl_f_expr AP F,
    (bnd e <= 2 ^ (5 * sz e * sz e))%nat.
  Proof.
    intros e.
    induction e as [ | | p | l f IH | e0 IH | e1 e2 IH ] using ltl_f_induction_principle.
    - cbn. lia.
    - cbn. lia.
    - cbn. lia.
    - destruct l as [| a l'].
      + cbn. lia.
      + apply f_term_bound_exponential; [| exact IH].
        cbn [ListDef.map sum_list_elements_nat].
        pose proof (expr_size_ge_1 a). lia.
    - cbn [ge_bound expr_size].
      apply pow2_le_mono with (j := (5 * sz e0 * sz e0 + 1)%nat).
      + apply pow2_add_le; [apply pow2_ge_1 | exact IH].
      + nia.
    - destruct IH as [IH1 IH2]. cbn [ge_bound expr_size].
      assert (H1 : (bnd e1 <= 2 ^ (5 * sz e1 * sz e1 + 5 * sz e2 * sz e2))%nat)
        by (apply pow2_le_mono with (j := (5 * sz e1 * sz e1)%nat); [exact IH1 | lia]).
      assert (H2 : (bnd e2 <= 2 ^ (5 * sz e1 * sz e1 + 5 * sz e2 * sz e2))%nat)
        by (apply pow2_le_mono with (j := (5 * sz e2 * sz e2)%nat); [exact IH2 | lia]).
      apply pow2_le_mono with
        (j := (5 * sz e1 * sz e1 + 5 * sz e2 * sz e2 + 1 + 1)%nat).
      + apply pow2_add_le.
        * apply pow2_add_le; [apply pow2_ge_1 | exact H1].
        * apply pow2_le_mono with
            (j := (5 * sz e1 * sz e1 + 5 * sz e2 * sz e2)%nat); [exact H2 | lia].
      + nia.
  Qed.

  (** The threshold translation is at most exponentially longer than the
      [ltl_f] formula it came from. *)
  Theorem ge_ltl_size_exponential : forall (e : ltl_f_expr AP F) (r : UnitInterval),
    (ltl_size AP (ge_ltl AP F f_to_function e r) <= 2 ^ (5 * sz e * sz e))%nat.
  Proof.
    intros e r. apply Nat.le_trans with (m := bnd e);
      [apply ge_ltl_size_le | apply ge_bound_exponential].
  Qed.

  (** And so is the set-membership translation, for any [P] whatever. *)
  Theorem in_ltl_size_exponential : forall (e : ltl_f_expr AP F) (P : list UnitInterval),
    (ltl_size AP (in_ltl AP F f_to_function e (trim AP F f_to_function e P))
     <= 2 ^ (5 * sz e * sz e + sz e + 3))%nat.
  Proof.
    intros e P.
    assert (Hp : (length (psv e) <= 2 ^ sz e)%nat)
      by apply possible_statsfaction_values_bounded.
    assert (Hb : (bnd e <= 2 ^ (5 * sz e * sz e))%nat) by apply ge_bound_exponential.
    assert (H2b : (2 * bnd e <= 2 ^ (1 + 5 * sz e * sz e))%nat)
      by (apply pow2_mul_le; [cbn; lia | exact Hb]).
    assert (H3 : (3 + 2 * bnd e <= 2 ^ (1 + 5 * sz e * sz e + 1))%nat).
    { apply pow2_add_le; [| exact H2b].
      apply pow2_le_mono with (j := 2%nat); [cbn; lia |].
      pose proof (expr_size_ge_1 e). nia. }
    assert (H4 : (length (psv e) * (3 + 2 * bnd e)
                  <= 2 ^ (sz e + (1 + 5 * sz e * sz e + 1)))%nat)
      by (apply pow2_mul_le; [exact Hp | exact H3]).
    assert (H5 : (1 + length (psv e) * (3 + 2 * bnd e)
                  <= 2 ^ (sz e + (1 + 5 * sz e * sz e + 1) + 1))%nat)
      by (apply pow2_add_le; [apply pow2_ge_1 | exact H4]).
    apply Nat.le_trans with
      (m := (1 + length (psv e) * (3 + 2 * bnd e))%nat);
      [apply in_ltl_trim_size_le |].
    apply pow2_le_mono with (j := (sz e + (1 + 5 * sz e * sz e + 1) + 1)%nat);
      [exact H5 | nia].
  Qed.

End closed_size_bound.
