
From stdpp Require Import gmap.
From stdpp Require Import base.
From stdpp Require Import countable strings.

Require Import formulas.
Require Import evaluation.


Fixpoint substitution (n : nat) (A B : prop) : prop :=
  match A with
  | Bot       => Bot
  | Top       => Top
  | Atom m    => if Nat.eqb m n then B else A
  | And P1 P2 => And (substitution n P1 B) (substitution n P2 B)
  | Or  P1 P2 => Or  (substitution n P1 B) (substitution n P2 B)
  | Imp P1 P2 => Imp (substitution n P1 B) (substitution n P2 B)
  | Neg P1    => Neg (substitution n P1 B)
  end.

Example sub1 : forall (n : nat) (p q A : prop),
  p ≡ q -> substitution n A p ≡ substitution n A q.
Proof.
intros. apply equive_eq in H. apply equive_eq.
unfold equivalence2 in H. unfold equivalence2.
induction A.
-simpl. reflexivity.
-simpl. reflexivity.
-simpl. destruct (n0 =? n) eqn:h1.
  +apply H.
  +simpl. intro. reflexivity.
-intros. simpl. split.
  + intros. specialize IHA1 with (I := I). specialize IHA2 with (I := I).
   apply andb_true_iff in H0. destruct H0.
   apply andb_true_iff. split. apply IHA1. apply H0. apply IHA2. apply H1.
  + intros. specialize IHA1 with (I := I). specialize IHA2 with (I := I).
   apply andb_true_iff in H0. destruct H0.
   apply andb_true_iff. split. apply IHA1. apply H0. apply IHA2. apply H1.
-intros. simpl. split.
  + intros. specialize IHA1 with (I := I). specialize IHA2 with (I := I).
Admitted.





Example sub2 : forall (p q:nat) (A : prop),
    {[Atom p]} ⊨₃ A <-> ⊨₀ (substitution p A (Imp (Atom q) (Atom q)) ).
Proof.
intros.
split.
-unfold model3. unfold taut. unfold model2. unfold model1.
intros.
Admitted.


Theorem substitution_tautology :
  forall (n:nat) (A B : prop), ⊨₀ A -> ⊨₀ substitution n A B.
Proof.
unfold taut. unfold model1. intros. simpl.
induction A.
-simpl. specialize H with (I := I). rewrite <- H. reflexivity.
-simpl. specialize H with (I := I). rewrite <- H. reflexivity.
-simpl. destruct (n0 =? n) eqn:h1.
  + pose (F := fun n => if Nat.eqb n n0 then false else true).
  assert (h2 : interpret F (Atom n0) = false). { simpl. unfold F.
  rewrite (Nat.eqb_refl n0). reflexivity. }
  specialize H with (I := F). rewrite H in h2. inversion h2.
  +specialize H with (I := I). assumption.
-simpl.
Admitted.



Theorem substitution_by_equivalence_props (p q A : prop) (I : eval_fun) (x : nat):
  (p ≡₂ q) ->
  (interpret I (substitution x A p) = true) ->
  (interpret I (substitution x A q) = true).
Proof.
unfold equivalence2. intros.
induction A.
-simpl. simpl in H0. assumption.
-reflexivity.
-simpl. destruct (n =? x) eqn:m.
  +simpl in H0. rewrite m in H0. apply H. assumption.
  +simpl. simpl in H0. rewrite m in H0. simpl in H0. assumption.
-simpl. apply andb_true_iff. simpl in H0. apply andb_true_iff in H0. destruct H0. split.
  +apply IHA1. apply H0.
  +apply IHA2. apply H1.
-simpl. apply orb_true_iff. simpl in H0. apply orb_true_iff in H0. destruct H0.
  + left. apply IHA1. apply H0.
  + right. apply IHA2. apply H0.

Admitted.
