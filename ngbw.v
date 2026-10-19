From Stdlib Require Import List.
From Stdlib Require Import Streams.
From Stdlib Require Import Lia.

Section NGBW.

Variable Alphabet : Type.
Variable State : Type.
Variable TransistionFunction: Alphabet -> State -> (State -> Prop).
Variable IntialState : State -> Prop.
Variable FinalStates : (State -> Prop) -> Prop.

Definition allStatesReachble (run : Stream State) (word : Stream Alphabet) := 
  forall i, TransistionFunction (Str_nth i word) (Str_nth i run) (Str_nth (i + 1) run).

Definition isRunOnWord (run : Stream State) (word : Stream Alphabet) : Prop := 
    IntialState (hd run) /\ allStatesReachble run word.

Definition satisfied_by_on (word : Stream Alphabet) (run : Stream State) :=
  isRunOnWord run word /\ 
  (forall (set : State -> Prop), FinalStates set -> forall i, exists k, i <= k /\ set (Str_nth k run)). 

End NGBW .

Inductive Alphabet : Type :=
  | a
  | b
  | c.

Inductive State : Type :=
  | q0
  | q1.

Definition accept (state : State) : State -> Prop :=
  fun s => s = state.

Definition TransistionFunction (letter : Alphabet) (state : State ) : State -> Prop := 
match state, letter with
  |  q0, a => (accept q0)
  |  q0, b => (accept q1)
  |  q1, c => (accept q1)
  |  _, _ => fun s => False
end.

Definition IntialState (state : State) :=
match state with
  | q0 => True
  | q1 => False
end.

Definition q1Set (state : State) :=   
match state with
  | q0 => False
  | q1 => True
end.

Definition FinalState (set : State -> Prop) :=
  set = q1Set.

CoFixpoint c_stream : Stream Alphabet := Cons c c_stream.

Definition test_word : Stream Alphabet := Cons a (Cons b c_stream).

CoFixpoint q1_stream : Stream State := Cons q1 q1_stream.

Definition test_run : Stream State := Cons q0 (Cons q0 q1_stream).

Lemma nth_tl_c_stream : forall i, Str_nth_tl i c_stream = c_stream .
Proof. induction i; simpl; auto. Qed.

Lemma nth_tl_q1_stream : forall i, Str_nth_tl i q1_stream = q1_stream.
Proof. induction i; simpl; auto. Qed.

Lemma q1_stream_always_q1 : forall i, Str_nth i q1_stream = q1.
  intros i. rewrite (unfold_Stream q1_stream).  simpl. induction i.
  + auto.
  + unfold Str_nth. simpl. rewrite nth_tl_q1_stream. auto.
Qed.

Theorem testNGBW : satisfied_by_on Alphabet State TransistionFunction IntialState FinalState test_word test_run.
Proof.
   split. 
  + split. 
    - simpl. reflexivity.
    - intros i. destruct i as [|i']. 
      * unfold Str_nth. simpl. reflexivity.
      * destruct i' as [|i''].
        ++ unfold Str_nth. simpl. reflexivity. 
        ++ simpl. unfold Str_nth. simpl. 
           rewrite nth_tl_c_stream. 
           rewrite nth_tl_q1_stream. 
           rewrite nth_tl_q1_stream.
           simpl. reflexivity.
  + intros set Hfinal. unfold FinalState in Hfinal. rewrite Hfinal. intros i.
    exists (i + 2). split. lia. rewrite (unfold_Stream test_run). simpl. rewrite <- Str_nth_plus. simpl.
    rewrite q1_stream_always_q1. simpl. apply I.
Qed.

