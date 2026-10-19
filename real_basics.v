Parameter R : Set.

Delimit Scope R_scope with R.
Local Open Scope R_scope.
 
(* Parameter and axiom are the same thing*)
Parameter R0 : R.
Parameter R1  : R.

Parameter Rplus : R -> R -> R.
Parameter Rmult : R -> R -> R.
Parameter Ropp : R -> R.
Parameter Rinv : R -> R.

Infix "+" := Rplus : R_scope.
Infix "*" := Rmult : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Notation "/ x" := (Rinv x) : R_scope.

Definition Rminus (r1 r2:R) : R := r1 + - r2.
Definition Rdiv (r1 r2:R) : R := r1 * / r2.

Infix "-" := Rminus : R_scope.
Infix "/" := Rdiv : R_scope.

(* Natural numbers to real numbers *)
Fixpoint INR (n : nat) : R :=
  match n with 
  | 0 => R0
  | 1 => R1
  | S n' => R1 + INR n'
  end.

Fail Check (4 + 5).

Coercion INR :  nat >-> R.

Check 4 + 5.
Compute (4 + 5).

Axiom R1_neq_R0 : INR 1 <> INR 0.
Axiom Rplus_comm: forall (r1 r2 : R), r1 + r2 = r2 + r1.
Axiom Rplus_assoc : forall (r1 r2 r3:R), r1 + r2 + r3 = r1 + (r2 + r3).
Axiom Rplus_opp_r : forall (r:R), r + - r = 0.
Axiom Rplus_0_l : forall (r:R), 0 + r = r.

Lemma Rplus_0_r : forall r:R, r + 0 = r.
Proof.
  intros r.
  rewrite Rplus_comm.
  apply Rplus_0_l.
Qed.

Lemma Rplus_opp_l : forall r : R, -r + r = 0.
Proof.
  intros r.
  rewrite Rplus_comm.
  apply Rplus_opp_r.
Qed.

Lemma Ropp_0 : - 0 = 0.
Proof.
  rewrite <- (Rplus_0_l (- 0)).
  rewrite Rplus_opp_r.
  reflexivity.
Qed.

Lemma Rplus_cancel_l : forall r1 r2 r3, r1 + r2 = r1 + r3 -> r2 = r3.
Proof.
  intros r1 r2 r3 H.
  rewrite <- Rplus_0_l.
  rewrite <- (Rplus_opp_l r1).
  rewrite Rplus_assoc.
  rewrite <- H. 
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.

Lemma R0_unique : forall r1 r2 :R, r1 + r2 = r1 -> r2 = 0.
Proof.
  intros r1 r2 H.
  rewrite <- Rplus_0_r in H.
  apply Rplus_cancel_l in H.
  apply H.
Qed.

Axiom Rmult_comm : forall r1 r2 : R, r1 * r2 = r2 * r1.
Axiom Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 = r1 * ( r2 * r3 ).
Axiom Rinv_l : forall r: R, r <> 0 -> / r * r = 1. 
Axiom Rmult_1_l : forall r : R, 1 * r = r.
Axiom Rmult_plus_distr_l : forall r1 r2 r3 : R, r1 * (r2 + r3) = r1 * r2 + r1 * r3.

Lemma  Rmult_0_r : forall r : R, r * 0 = 0.
Proof.
  intros r.
  apply (R0_unique (r * 0)).
  rewrite <- Rmult_plus_distr_l.
  rewrite (Rplus_0_r 0).
  reflexivity.
Qed.

Lemma Rmult_plus_distr_r : forall r1 r2 r3: R, (r1 + r2) * r3 = r1 * r3 + r2 * r3.
Proof.
  intros r1 r2 r3.
  rewrite Rmult_comm.
  rewrite Rmult_plus_distr_l.
  rewrite (Rmult_comm r3 r1).
  rewrite (Rmult_comm r3 r2).
  reflexivity.
Qed.

Lemma Rinv_r : forall r : R, r <> 0 -> r * / r = 1.
Proof.
  intros r H.
  rewrite Rmult_comm.
  apply Rinv_l in H.
  apply H.
Qed.

From Stdlib Require Export Ring.
From Stdlib Require Export Field.

Lemma R_Ring_Theory : ring_theory R0 R1 Rplus Rmult Rminus Ropp eq.
Proof.
  constructor.
  - apply Rplus_0_l.
  - apply Rplus_comm.
  - intros x y z. rewrite Rplus_assoc. reflexivity.
  - apply Rmult_1_l.
  - apply Rmult_comm.
  - intros x y z. rewrite Rmult_assoc. reflexivity.
  - apply Rmult_plus_distr_r.
  - reflexivity.
  - apply Rplus_opp_r.
Qed.
 
Add Ring RRing : R_Ring_Theory.

Lemma R_Field_Theory : field_theory R0 R1 Rplus Rmult Rminus Ropp Rdiv Rinv eq.
Proof. 
  constructor.
  apply R_Ring_Theory.
  apply R1_neq_R0.
  reflexivity.
  apply Rinv_l. 
Qed. 

Add Field RField : R_Field_Theory.

Example ring_test1 : forall (x : R), x + x = 2 * x. Proof. intros. simpl. ring. Qed.
Example ring_test2 : forall (x y z : R), x * y + z = z + y * x. Proof. intros. ring. Qed.
 
Example field_test1 : forall (x y : R), x <> 0 -> x * y / x = y.
Proof. intros. Fail ring. field. apply H. Qed.

Parameter Rlt : R -> R -> Prop.

Infix "<" := Rlt : R_scope.

Definition Rgt (r1 r2:R) : Prop := r2 < r1.
Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.
Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 = r2.

Infix "<=" := Rle : R_scope.
Infix ">=" := Rge : R_scope.
Infix ">" := Rgt : R_scope.

Axiom total_order_T : forall r1 r2 : R, {r1 < r2 } + { r1 = r2} + {r1 > r2}.
Axiom Rlt_asym : forall r1 r2: R, r1 < r2 -> ~ r2 < r1.
Axiom Rlt_trans : forall r1 r2 r3: R, r1 < r2 -> r2 < r3 -> r1 < r3.
Axiom Rplus_lt_compat_l: forall r r1 r2: R, r1 < r2 -> r + r1 < r + r2.
Axiom Rmult_lt_compat_l: forall r r1 r2: R, 0 < r1 -> r1 < r2 -> r * r1 < r * r2.

Definition is_upper_bound (E: R -> Prop) (m : R) := forall x : R, E x -> x <= m.
Definition bound (E:R -> Prop) := exists m : R, is_upper_bound E m.
Definition is_lub (E: R -> Prop) (m:R) := 
  is_upper_bound E m /\ (forall b : R, is_upper_bound E b -> m <= b).

Axiom completeness: forall E : R -> Prop, 
  bound E -> (exists x : R , E x) -> { m: R | is_lub E m}.
 
(* TODO(Simon) Proof this at some point *)
Lemma Rlt_0_1: 0 < 1. Admitted.

Definition lt_sqrt2 (x : R) := x * x < 2.

Lemma upper_bound_2_sqrt_2 : is_upper_bound lt_sqrt2 2. 
Proof. 
  unfold is_upper_bound, lt_sqrt2; simpl. 
  intros x H.
  left.
  destruct (total_order_T x 1) as [[L | E] | G].
  - apply (Rlt_trans _ 1 _).
    apply L.
    rewrite <- (Rplus_0_r 1).
    apply Rplus_lt_compat_l.
    apply Rlt_0_1.
  - rewrite E.
    rewrite <- (Rplus_0_r 1).
    apply Rplus_lt_compat_l.
    apply Rlt_0_1. 
  - assert (x*1 < x*x).
    + apply Rmult_lt_compat_l.
      apply Rlt_0_1.
      apply G.
    + rewrite Rmult_comm in H0.
      rewrite Rmult_1_l in H0.
      apply (Rlt_trans _ (x*x) _).
      apply H0.
      apply H.
Qed.

Lemma bound_sqrt2 : bound lt_sqrt2.
Proof. exists 2. apply upper_bound_2_sqrt_2. Qed.

Lemma ex_lt_sqrt2 : exists x, lt_sqrt2 x.
Proof.
  exists 1. unfold lt_sqrt2.
  rewrite Rmult_1_l.
  rewrite <- (Rplus_0_r 1).
  simpl.
  apply Rplus_lt_compat_l.
  apply Rlt_0_1.
Qed.

Definition sqrt2 := completeness lt_sqrt2 bound_sqrt2 ex_lt_sqrt2.
 
Check sqrt2.


(* I am a computer scientist using rocq as part of my research into rational verification. This requires a good understanding of 
how it handles real numbers. I have little exprience with "normal" axiomatic real numbers and little exprience of real analysis. 
I have a basic understanding of calculus and a good understanding of discrete mathmatics. I have through the logical foundations 
book on rocq.

The above as I understand is the implementation of real numbers in rocq's standard library. And a a couple small examples of it use.
There are a few rocq specific things conufusing me. First off what is a paramter and secondly what is a Set in line 1. The rest I will
now try to explain in plainish english. We define real numbers as the set R, we then open a scope in rocq to define syntax relevant to 
real numbers and declare we are uising the scope. We then define 2 two members of the set R 0 and 1 and four functions that can be used
to get real numbers if we already have 1 or 2 real numbers i.e. + * - /. We then define syntax for this. (are parametes here similiar 
to constructors on an inductive if not in what way are they different). We then define a conversion and coerion from natural numbers to 
real numbers, and show that it works.

We then define easy to accept as true axioms for axoims for reals and derive lemmas's proofing other things we care to be true hold under 
these axioms. (Is there any work showing that these axioms are equivalent to "normal" real numbers, and how are nomal real numbers defined).
We then show that these axioms form a ring and a field, and tell rocq about makint the ring and field tatics work to help automate proofs.
We the define axioms for ordering real numbers and the axiom of completness. Which I understand to say, given a set of reals E and a proof 
that it is bounded there is a real numver m which is its upper bounded. We  then use this rule to get the sqrt of 2.

(How correct is this explantion) *)
