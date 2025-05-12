
From stdpp Require Import gmap.
From stdpp Require Import base.
From stdpp Require Import countable strings.

Require Import formulas.
Require Import evaluation.
Require Import substitution.
Require Import propositional_symbols.

(*
interpolation theorem for the propositional logic!
*)

Definition interpolation_condition (A B : proposition) :=
  (∃ q : nat, q ∈ ps( A ) ∧ q ∈ ps( B )) ∧ (⊨₀ Imp A B).

Definition interpolation_statement (A B : proposition) :=
  ∃ C : proposition , (⊨₀ Imp A C) ∧ (⊨₀ Imp C B) ∧ ( ps( C ) ⊆ ps( A ) ∪ ps( B )).

Lemma induction_on_X (A B : proposition) :
  interpolation_condition A B
->
  (
    (ps(A) ⊆ ps(B)) -> interpolation_statement A B
  )
->
  (
    (
      forall A'' : proposition,
      ps(A'') = ps(A) -> interpolation_statement A'' B
    )
    ->
    (
      forall A' : proposition,
      (∃ m:nat, ps(A') = ps(A) ∪ {[m]}) -> interpolation_statement A' B
    )
  )
->
  interpolation_statement A B.
Proof.
Admitted.


Theorem interpolation_theorem (A B : proposition) :
interpolation_condition A B -> interpolation_statement A B.
Proof.
intros.
apply induction_on_X.

(*having the interpolation condition*)
-apply H.

(*base case of the induction*)
-intro. unfold interpolation_condition in H. unfold interpolation_statement.
destruct H. destruct H. destruct H.
exists A. split. apply taut4. split. apply H1. set_solver.

(*step case of the induction*)
-intros. destruct H1 as [p H1]. unfold interpolation_condition in H.
destruct H. destruct H as [q H]. destruct H.

(*defining three new propositions*)
set (A₁ := substitution p A' (Imp (Atom q) (Atom q))).
set (A₂ := substitution p A' (Neg (Imp (Atom q) (Atom q))) ).
set (A₃ := Or A₁ A₂).

unfold interpolation_statement. exists A₃. split.

Qed.
