Section stream.
  Variable A : Type.
  
  CoInductive stream : Type := 
  | Cons : A -> stream -> stream.

End stream.

Arguments Cons {A}. (* Infer A in Cons*)

CoFixpoint zeroes : stream nat := Cons 0 zeroes.

CoFixpoint trues_falses : stream bool := Cons true falses_trues 
with falses_trues : stream bool := Cons false trues_falses.

Fixpoint approx A (s : stream A) (n: nat) : list A :=
  match n with 
  | 0 => nil
  | S n' => match s with 
            | Cons h t => h :: approx A t n'
            end
  end.

Arguments approx {A}.

Eval simpl in approx zeroes 10.
Eval simpl in approx trues_falses 10.

(* Illegal *)
(*CoFixpoint looper : stream nat := looper.*)

(*The rule we have run afoul of here is that every co-recursive call must be guarded by a constructor; that is, every co-recursive call must be a direct argument to a constructor of the co-inductive type we are generating. It is a good thing that this rule is enforced. If the definition of looper were accepted, our approx function would run forever when passed looper, and we would have fallen into inconsistency.*)

Section map. 
  Variable A B : Type.
  Variable f : A -> B.

  CoFixpoint map (s : stream A) : stream B :=
    match s with 
    | Cons h t => Cons (f h) (map t)
    end.
End map.

Arguments map {A} {B}.

Section interleave. 
  Variable A : Type.

  CoFixpoint interleave (s1 s2 : stream A) : stream A :=
    match s1, s2 with 
    | Cons h1 t1, Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.

Arguments interleave {A}.

(*Section map'.*)
(*  Variables A B : Type.*)
(*  Variable f : A -> B.*)
(**)
(*  CoFixpoint map' (s : stream A) : stream B :=*)
(*    match s with *)
(*    | Cons h t => interleave (Cons (f h) (map' t)) (Cons (f h) (map' t))*)
(*    end.*)
(**)
(*End map'.*)

Definition tl A (s : stream A) : stream A :=
  match s with 
  | Cons _ s' => s'
  end.

Arguments tl {A}.

(* Illegal *)
(*CoFixpoint bad : stream nat := tl (Cons 0 bad).*)

(*Coq's complete rule for co-recursive definitions includes not just the basic guardedness condition, but also a requirement about where co-recursive calls may occur. In particular, a co-recursive call must be a direct argument to a constructor, nested only inside of other constructor calls or fun or match expressions. In the definition of bad, we erroneously nested the co-recursive call inside a call to tl, and we nested inside a call to interleave in the definition of map'.*)

(* Continue at Inifinite Proofs *)
CoFixpoint ones : stream nat := Cons 1 ones.
Definition ones' := map S zeroes.

Theorem ones_eq : ones = ones'.
Abort.

Section stream_eq.
  Variable A : Type.

  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : forall h t1 t2,
    stream_eq t1 t2 -> stream_eq (Cons h t1) (Cons h t2).
End stream_eq.

Arguments stream_eq {A}.

(* 
We can run the command Guarded in any context to see if it is possible to finish the proof in a way that will yield a properly guarded proof term.
   Guarded. *)

Theorem ones_eq : stream_eq ones ones'.
cofix ones_eq.
assumption.
Undo.
simpl.
Abort.

Definition frob A (s : stream A) : stream A :=
  match s with 
  | Cons h t => Cons h t
  end.

Arguments frob {A}.

Theorem frob_eq : forall A (s : stream A), s = frob s.
  destruct s; reflexivity.
Qed.

Arguments frob_eq {A}.

Theorem ones_eq : stream_eq ones ones'.
cofix ones_eq.
rewrite (frob_eq ones).
rewrite (frob_eq ones').
simpl.
apply Stream_eq.
assumption.
Qed.

Definition hd A (s : stream A) : A := 
  match s with 
  | Cons x _ => x
  end.

Arguments hd {A}.

(*Park's principle as introduced in a tutorial by Gimenez*)
(* bisumulation *)
Section stream_eq_coind.
  Variable A : Type.
  Variable R : stream A -> stream A -> Prop.
  Hypothesis Cons_case_hd : forall s1 s2, R s1 s2 -> hd s1 = hd s2.
  Hypothesis Cons_case_tl : forall s1 s2, R s1 s2 -> R (tl s1) (tl s2).

  Theorem stream_eq_coind : forall s1 s2, R s1 s2 -> stream_eq s1 s2.
    cofix stream_eq_coind; destruct s1; destruct s2; intro.
    generalize (Cons_case_hd (Cons a s1) (Cons a0 s2) H); intro Heq; simpl in Heq; rewrite Heq.
    constructor.
    apply stream_eq_coind.
    apply (Cons_case_tl (Cons a s1) (Cons a0 s2) H).
  Qed.
End stream_eq_coind.

Arguments stream_eq_coind {A}.

Print stream_eq_coind.
(* Continue form book*)
Theorem ones_eq'' : stream_eq ones ones'.
apply (stream_eq_coind (fun s1 s2 => s1 = ones /\ s2 = ones')).
  + intros s1 s2 [H H'] ; rewrite H ; rewrite H'.
    simpl; reflexivity.
  + intros s1 s2 [H H'] ; rewrite H ; rewrite H'.
    split ; simpl; reflexivity.
  + split ; simpl; reflexivity.
Qed.

Section stream_eq_loop.
  Variable A : Type.
  Variables s1 s2 : stream A.

  Hypothesis Cons_case_hd : hd s1 = hd s2.
  Hypothesis loop1 : tl s1 = s1.
  Hypothesis loop2 : tl s2 = s2.

  Theorem stream_eq_loop : stream_eq s1 s2.
    apply (stream_eq_coind (fun s1' s2' => s1' = s1 /\ s2' = s2)).
    + intros s0 s3 [H H'] ; rewrite H ; rewrite H'. apply Cons_case_hd.
    + intros s0 s3 [H H'] ; rewrite H ; rewrite H'.
      split ; assumption.
    + split ; reflexivity.
  Qed.
End stream_eq_loop.

Arguments stream_eq_loop {A}.

Theorem ones_eq''' : stream_eq ones ones'.
  apply stream_eq_loop ; simpl ; reflexivity.
Qed.

From Stdlib Require Import Arith.
Print fact.

CoFixpoint fact_slow' (n : nat) := Cons (fact n) (fact_slow' (S n)).
Definition fact_slow := fact_slow' 1.

CoFixpoint fact_iter' (cur acc : nat) := Cons acc (fact_iter' (S cur) (acc * cur)).
Definition fact_iter := fact_iter' 2 1.

Eval simpl in approx fact_iter 5.
Eval simpl in approx fact_slow 5.

Lemma fact_def : forall x n,
  fact_iter' x (fact n * S n) = fact_iter' x (fact (S n)).
simpl ; intros ; f_equal ; ring.
Qed.

Lemma fact_eq' : forall n, stream_eq (fact_iter' (S n) (fact n)) (fact_slow' n).
intros ; apply (stream_eq_coind (fun s1 s2 => exists n, s1 = fact_iter' (S n) (fact n) /\ s2 = fact_slow' n )).
  + intros s1 s2 [n1 [Hit Hsl]] ; rewrite Hit ; rewrite Hsl. simpl ; reflexivity.
  + intros s1 s2 [n1 [Hit Hsl]] ; rewrite Hit; rewrite Hsl. exists (S n1). split.
    - apply fact_def.
    - simpl. reflexivity.
  + exists n ; split ; reflexivity.
Qed.

Theorem fact_eq : stream_eq fact_iter fact_slow.
   apply fact_eq'.
Qed.

Section stream_eq_onequant.
  Variables A B : Type.
  Variables f g : A -> stream B.

  Hypothesis Cons_case_hd : forall x, hd (f x) = hd (g x).
  Hypothesis Cons_case_tl : forall x, exists y, tl (f x) = f y /\ tl (g x) = g y.

  Theorem stream_eq_onequant : forall x, stream_eq (f x) (g x).
  intros ; apply (stream_eq_coind (fun s1 s2 => exists x, s1 = f x /\ s2 = g x)).
  + intros s1 s2 [x1 [Hf Hg]] ; rewrite Hf ; rewrite Hg.
    apply Cons_case_hd.
  + intros s1 s2 [x1 [Hf Hg]] ; rewrite Hf ; rewrite Hg.
    apply Cons_case_tl.
  + exists x ; split ; reflexivity.
 Qed. 
End stream_eq_onequant.

Arguments stream_eq_onequant {A} {B}.

Lemma fact_eq'' : forall n, stream_eq (fact_iter' (S n) (fact n)) (fact_slow' n).
  apply stream_eq_onequant.
  + intros x ; simpl ; reflexivity.
  + intros x ; exists (S x) ; split.
    - apply fact_def.
    - simpl. reflexivity.
Qed.



