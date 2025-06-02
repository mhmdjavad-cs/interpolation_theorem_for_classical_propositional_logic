
From stdpp Require Import gmap.
From stdpp Require Import base.
From stdpp Require Import countable strings.
Require Import stdpp.sets.
Require Import Lia.

Require Import formulas.
Require Import evaluation.
Require Import substitution.
Require Import deduction.
Require Import hilbert_system.


(*
this file contains the proof of completeness1
and completeness2 theorems, some theorems about sets
and proof of the transitivity of proofs.
*)




(* completeness theorems for our proof system *)
Theorem completeness1 (q : prop) :
  (⊨₀ q) -> (∅ ⊢ q).
Proof.
Admitted.






Lemma card_zero_eq_empty (Γ : context) :
  size (Γ) = 0 <-> Γ = ∅.
Proof.
split.
-intro.
apply leibniz_equiv.
apply size_empty_iff with (X:= Γ).
assumption.
-intro. rewrite H. reflexivity.
Qed.


Lemma model3_eq_taut (p : prop):
  (∅ ⊨₃ p) <-> (⊨₀ p).
Proof.
split.
-unfold model3. unfold model2. unfold taut. unfold model1.
intros. apply H. intros. inversion H0.
-unfold model3. unfold model2. unfold taut. unfold model1.
intros. apply H.
Qed.

(* Lemma card_not_zero_not_empty (Γ : context) (n : nat):
  (size (Γ) = S n) -> (Γ <> ∅).
Admitted. *)


Lemma one_element (Γ : context) (n : nat):
  (size (Γ) = S n) -> (∃ x : prop, (x ∈ Γ)).
Proof.
intros Hsize.
apply size_pos_elem_of.
rewrite Hsize.
apply Nat.lt_0_succ.      (* Prove 0 < S n using standard library *)
Qed.




Lemma getting_one_element (Γ : context) (x : prop) :
  x ∈ Γ -> (∃ Γ' : context , (Γ' ∪ {[x]} = Γ) ∧ (size Γ' = (size Γ) - 1) ).
Proof.
intros.
exists (difference Γ {[x]}).
split.
apply set_eq => y.                 (* Prove set equality by showing equal membership *)
split.
-intros. apply elem_of_union in H0. destruct H0.
apply elem_of_difference in H0. destruct H0. assumption.
apply elem_of_singleton in H0. rewrite H0. assumption.
-
destruct (decide (y = x)) as [->|Hne].  (* Case analysis: y = x or y ≠ x *)
  +intros. apply elem_of_union. right.
   set_solver.
  +intros. apply elem_of_union.
  left. apply elem_of_difference. split.
  assumption. unfold not. intros. apply elem_of_singleton in H1.
  apply Hne. assumption.

(*size Γ'*)
-rewrite size_difference. rewrite size_singleton. reflexivity.
set_solver.
Qed.




Theorem completeness2 (Γ : context) (q : prop) :
  (Γ ⊨₃ q) -> (Γ ⊢ q).
Proof.
remember (size ( Γ )) as n eqn:Heqn.
generalize dependent Γ.
generalize dependent q.
induction n.
-intros. symmetry in Heqn. apply card_zero_eq_empty in Heqn.
rewrite Heqn. simpl. intros.
rewrite Heqn in H. apply model3_eq_taut in H.
apply completeness1. assumption.
-intros.
pose proof Heqn as h1.
symmetry in h1. apply one_element in h1. destruct h1.
pose proof H0 as h1.
apply getting_one_element in h1. destruct h1. destruct H1.
rewrite <- Heqn in H2. simpl in H2. rewrite Nat.sub_0_r in H2.
rewrite <- H1. apply deduction_theorem.
apply IHn. symmetry. assumption.
apply deduction_theorem_semantical. rewrite H1. assumption.
Qed.


Example implication_is_transitive (A B C : prop) :
  (⊨₀ Imp A B) ->
  (⊨₀ Imp B C) ->
  (⊨₀ Imp A C).
Proof.
intros.
apply soundness2.
apply completeness1 in H.
apply completeness1 in H0.
apply imp_intro.
eapply proof_is_transitive.
-apply deduction_theorem in H.
instantiate (1 := B). assumption.
-apply deduction_theorem in H0. rewrite union_with_empty in H0. assumption.
Qed.
