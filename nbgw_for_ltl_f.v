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

Section nbgw_for_ltl_f.

  Variables AP F : Set.
  Variable f_to_f : F -> (list UnitInterval -> UnitInterval).

  Variable expression : ltl_f_expr AP F.
  Variable predicate : list UnitInterval.

  Fixpoint or_list_of_props (l : list Prop) := 
  match l with 
  | [] => False
  | p :: rest => p \/ or_list_of_props rest 
  end.

  Fixpoint isSubExpr (orginal : ltl_f_expr AP F) (potentialSubExpr : ltl_f_expr AP F) := 
  match orginal with
  | TRUE _ _ => potentialSubExpr = TRUE AP F
  | FALSE _ _ => potentialSubExpr = FALSE AP F
  | AP_TERM _ _ p => potentialSubExpr = AP_TERM AP F p
  | F_TERM _ _ f l => potentialSubExpr = F_TERM AP F f l \/ (or_list_of_props (ListDef.map (fun item => isSubExpr item potentialSubExpr)  l))
  | NEXT _ _ e1 => potentialSubExpr = NEXT AP F e1 \/ isSubExpr e1 potentialSubExpr
  | UNTIL _ _ e1 e2 => potentialSubExpr = UNTIL AP F e1 e2 \/ isSubExpr e1 potentialSubExpr \/ isSubExpr e2 potentialSubExpr
  end.

  (* Thanks claude*)
  Lemma isSubExpr_refl : forall e : ltl_f_expr AP F, isSubExpr e e.
  Proof. intros e; destruct e; simpl; try reflexivity; left; reflexivity. Qed.

  Lemma or_list_of_props_exists : forall {A} (P : A -> Prop) (l : list A),
    or_list_of_props (ListDef.map P l) <-> exists x, In x l /\ P x.
  Proof.
    induction l as [| a l IHl]; simpl.
    - split; [contradiction | intros [x [[] _]]].
    - split.
      + intros [Hp | Hrest].
        * exists a; auto.
        * apply IHl in Hrest as [x [Hin Hx]]; exists x; auto.
      + intros [x [[<-|Hin] Hx]]; [left; assumption | right; apply IHl; eauto].
  Qed.

  Lemma isSubExpr_trans : forall orig e1 e2 : ltl_f_expr AP F,
    isSubExpr orig e1 -> isSubExpr e1 e2 -> isSubExpr orig e2.
  Proof.
    intros orig.
    induction orig as [ | | ap | l f IH | e IH | e1' e2' IH] using ltl_f_induction_principle;
      intros e1 e2 H1 H2; simpl in H1.
    - subst e1; exact H2.
    - subst e1; exact H2.
    - subst e1; exact H2.
    - destruct H1 as [<- | Hor]; [exact H2 |].
      apply or_list_of_props_exists in Hor as [x [Hin Hx]]; simpl.
      right; apply or_list_of_props_exists; exists x; eauto using (IH x Hin e1 e2).
    - destruct H1 as [<- | H1]; [exact H2 | simpl; right; eauto].
    - destruct H1 as [<- | [H1|H1]]; [exact H2 | simpl; right; left; firstorder | simpl; right; right; firstorder].
  Qed.

  Lemma isSubExpr_next_child : forall e, isSubExpr (NEXT AP F e) e.
  Proof. intros; simpl; right; apply isSubExpr_refl. Qed.

  Lemma isSubExpr_until_child1 : forall e1 e2, isSubExpr (UNTIL AP F e1 e2) e1.
  Proof. intros; simpl; right; left; apply isSubExpr_refl. Qed.

  Lemma isSubExpr_until_child2 : forall e1 e2, isSubExpr (UNTIL AP F e1 e2) e2.
  Proof. intros; simpl; right; right; apply isSubExpr_refl. Qed.

  Lemma isSubExpr_FTerm_child : forall f l x, In x l -> isSubExpr (F_TERM AP F f l) x.
  Proof.
    intros; simpl; right; apply or_list_of_props_exists.
    exists x; auto using isSubExpr_refl.
  Qed.

  Definition consistent (state : ltl_f_expr AP F -> UnitInterval) := 
    (forall e, isSubExpr expression e ->
    (e = TRUE AP F -> state (e) = one) /\
    (e = FALSE AP F -> state (e) = zero) /\
    (forall p, e = AP_TERM AP F p -> (state (e) = zero \/ state (e) = one)) /\
    (forall f l, e = F_TERM AP F f l -> (state (e) = ((f_to_f f) (ListDef.map state l)))))
  .
 
  Definition Alphabet := (AP -> AtomicProposition).
  Definition State := {g : ltl_f_expr AP F -> UnitInterval | consistent g}. 

  Definition TransistionFunction (letter : Alphabet) (from : State) := 
    fun (to : State) => forall e, isSubExpr expression e -> (
    (forall ap, e = AP_TERM AP F ap -> ((letter ap = AP1 -> (proj1_sig from) e = one) /\ (letter ap = AP0 -> (proj1_sig from) e = zero))) /\
    (forall e1, e = (NEXT AP F e1) -> ((proj1_sig from) e = (proj1_sig to) (e1))) /\
    (forall e1 e2, e = (UNTIL AP F e1 e2) -> ((proj1_sig from) (UNTIL AP F e1 e2)) =
      unitinterval_max ((proj1_sig from) e2) (unitinterval_min ((proj1_sig from) e1) ((proj1_sig to) (UNTIL AP F e1 e2))))).

  Definition IntialState (state: State) := 
    In ((proj1_sig state) expression) predicate.

  Definition FinalState (e1 e2 : ltl_f_expr AP F) :=
    fun (state : State) => (proj1_sig state) (e2) = (proj1_sig state) (UNTIL AP F e1 e2).

  Definition FinalStates (finalSet : State -> Prop) :=
    exists e1 e2, isSubExpr expression (UNTIL AP F e1 e2) /\ (FinalState e1 e2) = finalSet.

  Let sat_val := sat_val AP F f_to_f.
  Let satisfied_by_on := satisfied_by_on Alphabet State TransistionFunction IntialState FinalStates.

End nbgw_for_ltl_f.

