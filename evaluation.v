
From stdpp Require Import gmap.
From stdpp Require Import base.
From stdpp Require Import countable strings.

Require Import formulas.

(*
evaluation and interpretation functions,
evaluation assigns a truth value to the atoms,
iterpretation on the other hand, assigns a truth value
to the well formed propositions.
*)

Definition eval_fun := nat -> bool.
Definition myeval : eval_fun :=  fun x : nat => true.

Definition implb (b1 b2 : bool) : bool :=
  if b1 then b2 else true.

Fixpoint interpret : eval_fun -> (prop -> bool) :=
  fun e p => match p with
  | Bot => false
  | Top => true
  | Atom n => e n
  | And p1 p2 => andb (interpret e p1) (interpret e p2)
  | Or p1 p2 => orb (interpret e p1) (interpret e p2)
  | Imp p1 p2 => implb (interpret e p1) (interpret e p2)
  | Neg p1 => negb (interpret e p1)
  end.



Lemma either_true_or_false (I : eval_fun) (p : prop) :
  {(interpret I p) = true} + {(interpret I p) = false}.
Proof.
destruct (interpret I p).
-left. reflexivity.
-right. reflexivity.
Qed.

Lemma interpret_and (I : eval_fun) (p1 p2 : prop):
  interpret I (And p1 p2) = true <-> (interpret I p1) ∧ (interpret I p2).
Proof.
Admitted.


Theorem only_atoms_matter :
forall p:prop, forall e1 e2:eval_fun, (forall n : nat , e1 n = e2 n) -> interpret e1 p = interpret e2 p.
Proof.
intros.
induction p.
-reflexivity.
-reflexivity.
-simpl. apply H.
-simpl. rewrite IHp1. rewrite IHp2. reflexivity.
-simpl. rewrite IHp1. rewrite IHp2. reflexivity.
-simpl. rewrite IHp1. rewrite IHp2. reflexivity.
-simpl. rewrite IHp. reflexivity.
Qed.


Definition model1 (I: eval_fun) (p : prop) := interpret I p = true.
Notation "I ⊨₁ p" := (model1 I p) (at level 50).


Example model_example : myeval ⊨₁ (And (Atom 1) (Atom 2)).
Proof.
unfold model1. simpl. unfold myeval. reflexivity.
Qed.


Definition model2 (I: eval_fun) (Γ : context) :=
  forall p:prop, p ∈ Γ -> I ⊨₁ p.
Notation "I ⊨₂ Γ" := (model2 I Γ) (at level 50).

Definition model3 (Γ : context) (p : prop) :=
  forall I:eval_fun , I ⊨₂ Γ -> I ⊨₁ p.
Notation "Γ ⊨₃ p" := (model3 Γ p) (at level 50).

Example model3_example : {[Atom 1]} ⊨₃ (Atom 1).
Proof.
unfold model3. unfold model2. unfold model1. intros.
specialize H with (p := (Atom 1)). apply H.
apply elem_of_singleton. reflexivity.
Qed.


Example model3_example2 :
  forall A B : prop, {[A; Imp A B]} ⊨₃ B.
Proof.
intros. unfold model3. unfold model2. unfold model1. intros.
destruct (interpret I B) eqn:h1. reflexivity.
assert (interpret I A = true).
{
  apply H. apply elem_of_union. left. apply elem_of_singleton. reflexivity.
}
assert (interpret I (Imp A B) = true).
{
  apply H. apply elem_of_union. right. apply elem_of_singleton. reflexivity.
}
assert (interpret I (Imp A B) = false).
{
  simpl. rewrite h1. rewrite H0. simpl. reflexivity.
}
rewrite H1 in H2. symmetry. assumption.
Qed.




Definition taut (p : prop) := forall I:eval_fun , I ⊨₁ p.
Notation "⊨₀ p" := (taut p) (at level 49).

Definition equivalence (p q : prop) := ⊨₀ And (Imp p q) (Imp q p).
Notation "A ≡ B" := (equivalence A B) (at level 70).

Definition equivalence2 (p q : prop) :=
  forall I : eval_fun, interpret I p = true <-> interpret I q = true.
Notation "A ≡₂ B" := (equivalence2 A B) (at level 70).


Lemma equive_eq (A B : prop): (A ≡ B) <-> (A ≡₂ B).
Proof.
unfold equivalence. unfold equivalence2. unfold taut. unfold model1.
split.
-intros. split.
  + intros. simpl in H. specialize H with (I := I). rewrite H0 in H. simpl in H.
  apply andb_prop in H. destruct H. apply H.
  + intros. simpl in H. specialize H with (I := I). rewrite H0 in H. simpl in H.
  apply andb_prop in H. destruct H. apply H1.
- intros. simpl. unfold implb. specialize H with (I := I). destruct (interpret I A) eqn:h1.
  +destruct H. assert (h2 : interpret I B = true). {apply H. reflexivity. }
  rewrite h2. reflexivity.
  +destruct (interpret I B) eqn:h2. inversion H. simpl. apply H1. reflexivity. reflexivity.
Qed.



Example taut1 : ⊨₀ Imp (Atom 0) (Atom 0).
Proof.
unfold taut.
intros. unfold model1. simpl. unfold implb.
destruct (I 0) ; reflexivity.
Qed.

Example taut2 : ⊨₀ Or (Neg (Atom 0)) (Atom 0).
Proof.
unfold taut.
intros. unfold model1. simpl. destruct (I 0). simpl. reflexivity. simpl. reflexivity.
Qed.


Example taut3 :
  forall p : prop, ⊨₀ Or (Neg p) (p).
Proof.
unfold taut.
intros. unfold model1. simpl. destruct (interpret I p) eqn:h1.
simpl. reflexivity. simpl. reflexivity.
Qed.

Example taut4 :
  forall p : prop, ⊨₀ Imp p p.
Proof.
unfold taut.
intros. unfold model1. simpl. destruct (interpret I p) eqn:h1.
simpl. reflexivity. simpl. reflexivity.
Qed.


Example always_true (p : prop) : Top ≡₂ Imp p p.
Proof.
unfold equivalence2. intros.
split.
-intro. simpl. destruct (interpret I p) eqn:m.
reflexivity. reflexivity.
-intro. reflexivity.
Qed.

Example always_false (p : prop) : Bot ≡₂ Neg (Imp p p).
Proof.
unfold equivalence2. split.
-simpl. intro. inversion H.
-simpl. destruct (interpret I p) eqn:m.
simpl. intro. assumption. simpl. intro. assumption.
Qed.
