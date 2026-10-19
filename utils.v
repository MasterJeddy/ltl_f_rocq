From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import List.

Open Scope R_scope.

(** ** Utilities
  A collection of generic types and lemmas used throughout the formalism

 *** Real Subtype definitions and Lemmas
   This section defines two subtypes (subsets) of the real numbers central to the ltl-f formalism and its proofs.

 **** UnitInterval
  [UnitInterval] is the subtype of [R] which defines a real number between 1 and 0.
*)

Definition UnitInterval := { r : R | 0 <= r <= 1 }.

(** A lemma proofing that 1 is in [UnitInterval]*)
Lemma oneInUnitInterval : 0 <= 1 <= 1.
Proof.
  split. 
  apply Rlt_le.
  apply Rlt_0_1.
  apply Rle_refl.
Qed.

(** A lemma proofing that 0 is in [UnitInterval] *)
Lemma zeroInUnitInterval : 0 <= 0 <= 1.
Proof.
  split.
apply Rle_refl.
  apply Rlt_le.
  apply Rlt_0_1.
Qed.

Theorem unit_interval_min_proof : forall u1 u2 : UnitInterval, 0 <= Rmin (proj1_sig u1) (proj1_sig u2) <= 1.
 intros [r1 p1] [r2 p2]. simpl. unfold Rmin. destruct (Rle_dec r1 r2) ; assumption. 
Qed.

Definition unitinterval_min (u1 u2 : UnitInterval) : UnitInterval :=
  exist _ (Rmin (proj1_sig u1) (proj1_sig u2)) (unit_interval_min_proof u1 u2).

Theorem unit_interval_max_proof : forall u1 u2 : UnitInterval, 0 <= Rmax (proj1_sig u1) (proj1_sig u2) <= 1.
 intros [r1 p1] [r2 p2]. simpl. unfold Rmax. destruct (Rle_dec r1 r2) ; assumption. 
Qed.

Definition unitinterval_max (u1 u2 : UnitInterval) : UnitInterval :=
  exist _ (Rmax (proj1_sig u1) (proj1_sig u2)) (unit_interval_max_proof u1 u2).

Lemma unitinterval_eq : forall u1 u2 : UnitInterval, proj1_sig u1 = proj1_sig u2 -> u1 = u2.
Proof. intros [r1 p1] [r2 p2] H. simpl in H. subst r2. f_equal. apply proof_irrelevance. Qed.

Theorem unitinterval_max_case : forall u1 u2 : UnitInterval,
  unitinterval_max u1 u2 = u1 \/ unitinterval_max u1 u2 = u2.
Proof.
  intros [r1 p1] [r2 p2]. unfold unitinterval_max. simpl.
  destruct (Rle_dec r2 r1) as [Hle | Hgt].
  - left. apply unitinterval_eq. apply Rmax_left. assumption.
  - right. apply unitinterval_eq. apply Rmax_right. simpl. lra.
Qed.

Theorem unitinterval_min_case : forall u1 u2 : UnitInterval,
  unitinterval_min u1 u2 = u1 \/ unitinterval_min u1 u2 = u2.
Proof.
  intros [r1 p1] [r2 p2]. unfold unitinterval_min. simpl.
  destruct (Rle_dec r1 r2) as [Hle | Hgt].
  - left. apply unitinterval_eq. apply Rmin_left. assumption.
  - right. apply unitinterval_eq. apply Rmin_right. simpl. lra.
Qed.

(** Bounds and case-selection for [unitinterval_min]/[unitinterval_max], stated at the
    [UnitInterval] level so proofs can stay there instead of projecting out to [R]. *)

Lemma ui_max_l : forall a b, proj1_sig a <= proj1_sig (unitinterval_max a b).
Proof. intros; apply Rmax_l. Qed.

Lemma ui_max_r : forall a b, proj1_sig b <= proj1_sig (unitinterval_max a b).
Proof. intros; apply Rmax_r. Qed.

Lemma ui_min_l : forall a b, proj1_sig (unitinterval_min a b) <= proj1_sig a.
Proof. intros; apply Rmin_l. Qed.

Lemma ui_min_r : forall a b, proj1_sig (unitinterval_min a b) <= proj1_sig b.
Proof. intros; apply Rmin_r. Qed.

Lemma ui_max_is_l : forall a b, proj1_sig b <= proj1_sig a -> unitinterval_max a b = a.
Proof. intros a b H. apply unitinterval_eq. apply Rmax_left. exact H. Qed.

Lemma ui_max_is_r : forall a b, proj1_sig a <= proj1_sig b -> unitinterval_max a b = b.
Proof. intros a b H. apply unitinterval_eq. apply Rmax_right. exact H. Qed.

Lemma ui_min_is_l : forall a b, proj1_sig a <= proj1_sig b -> unitinterval_min a b = a.
Proof. intros a b H. apply unitinterval_eq. apply Rmin_left. exact H. Qed.

Lemma ui_min_is_r : forall a b, proj1_sig b <= proj1_sig a -> unitinterval_min a b = b.
Proof. intros a b H. apply unitinterval_eq. apply Rmin_right. exact H. Qed.

Lemma fold_left_max_in : forall (x : UnitInterval) (xs : list UnitInterval),
  In (fold_left unitinterval_max xs x) (x :: xs).
Proof.
  intros x xs. revert x.
  induction xs as [| y ys IH]; intros x.
  - simpl. left. reflexivity.
  - simpl. destruct (unitinterval_max_case x y) as [Heq | Heq]; rewrite Heq.
    + destruct (IH x) as [Heq2 | Hin2]; [left; assumption | right; right; assumption].
    + destruct (IH y) as [Heq2 | Hin2]; [right; left; assumption | right; right; assumption].
Qed.

Lemma fold_left_max_upper_bound : forall (x : UnitInterval) (xs : list UnitInterval) (y : UnitInterval),
  In y (x :: xs) -> proj1_sig y <= proj1_sig (fold_left unitinterval_max xs x).
Proof.
  intros x xs. revert x.
  induction xs as [| z zs IH]; intros x y Hin.
  - simpl in Hin. destruct Hin as [Heq | []]. subst y. apply Rle_refl.
  - simpl. destruct Hin as [Heq | [Heq | Hin]].
    + subst y. eapply Rle_trans.
      * unfold unitinterval_max; simpl; apply Rmax_l.
      * apply (IH (unitinterval_max x z) (unitinterval_max x z)). left. reflexivity.
    + subst y. eapply Rle_trans.
      * unfold unitinterval_max; simpl; apply Rmax_r.
      * apply (IH (unitinterval_max x z) (unitinterval_max x z)). left. reflexivity.
    + apply (IH (unitinterval_max x z) y). right. exact Hin.
Qed.


(** Two concrete members of the type [UnitInterval] for 0 and 1 *)
Definition zero : UnitInterval := exist _ 0 zeroInUnitInterval.
Definition one : UnitInterval := exist _ 1 oneInUnitInterval.

(**
 **** AtomicProposition
  [AtomicProposition] is the subtype of [R] which contains only the real numbers 0 and 1.
*)
Definition AtomicProposition := {r : R | r = 0 \/ r = 1}.

(** A lemma proofing that 1 is in [AtomicProposition]*)
Lemma oneIsZeroOrOne : 1 = 0 \/ 1 = 1.
Proof.
  right.
  reflexivity.
Qed.

(** A lemma proofing that 0 is in [AtomicProposition]*)
Lemma zeroIsZeroOrOne : 0 = 0 \/ 0 = 1. 
Proof.
  left.
  reflexivity.
Qed.

(** Two concrete members of the type [AtomicProposition] for 0 and 1 *)
Definition AP0 : AtomicProposition := exist _ 0 zeroIsZeroOrOne.
Definition AP1 : AtomicProposition := exist _ 1 oneIsZeroOrOne.

(** A lemma which prooves that members of [AtomicProposition] is either equivalent to [AP0] or [AP1] *)
Lemma atomic_proposition_one_or_zero : forall ap : AtomicProposition, ap = AP0 \/ ap = AP1.
Proof.
  intro ap. destruct ap as [r H]. destruct H as [H | H].
  - subst r. left. apply f_equal. apply proof_irrelevance.
  - subst r. right. apply f_equal. apply proof_irrelevance.
Qed.

(** A lemma which prooves that all members of [AtomicProposition] are also members of [UnitInterval]*)
Lemma atomic_to_interval_proof (r : R) : 
  r = 0 \/ r = 1 -> 0 <= r <= 1.
Proof.
  intros [H | H].
  - subst; lra.
  - subst; lra.
Qed.

(** A computational function which converts any [AtomicProposition] to a [UnitInterval]*)
Definition atomic_to_unit (ap : AtomicProposition) : UnitInterval := 
  match ap with 
  | exist _ r proof => exist (fun r => 0 <= r <= 1) r (atomic_to_interval_proof r proof)
  end.

(**
 *** FiniteEnum Class
   A type class capuring the the idea of a finite set i.e. a set for which a list can be constructed which contains all elements of the type. [FiniteEnum] also enforces that all memebers of the type can be distinguished from the others.
*)
Class FiniteEnum (T : Set) := {
  enum : list T;
  enum_complete : forall x : T, In x enum;
  eqb : T -> T -> bool;
  eqb_spec : forall x y : T, eqb x y = true <-> x = y
}.
