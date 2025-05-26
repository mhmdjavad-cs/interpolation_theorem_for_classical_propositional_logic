
From stdpp Require Import gmap.
From stdpp Require Import base.
From stdpp Require Import countable strings.
From Coq Require Import Bool.


Require Import formulas.
Require Import evaluation.
Require Import substitution.
Require Import propositional_symbols.
Require Import deduction.



Theorem validity_preserving1 (A B : prop) (n : nat):
  ⊨₀ Imp A B -> ⊨₀ Imp (substitution n A Top) B.
Proof.
Admitted.

Theorem validity_preserving2 (A B : prop) (n : nat):
  ⊨₀ Imp A B -> ⊨₀ Imp (substitution n A Bot) B.
Proof.
Admitted.




(*
interpolation theorem for the propositional logic!
*)

Definition interpolation_condition (A B : prop) :=
  (∃ q : nat, q ∈ ps( A ) ∧ q ∈ ps( B )) ∧ (⊨₀ Imp A B).

Definition interpolation_statement (A B : prop) :=
  ∃ C : prop , (⊨₀ Imp A C) ∧ (⊨₀ Imp C B) ∧ ( ps( C ) ⊆ ps( A ) ∪ ps( B )).

Lemma induction_on_X (A B : prop) :
  interpolation_condition A B
->
  (
    (ps(A) ⊆ ps(B)) -> interpolation_statement A B
  )
->
  (
    (
      forall A'' : prop,
      ps(A'') = ps(A) -> interpolation_statement A'' B
    )
    ->
    (
      forall A' : prop,
      (interpolation_condition A' B) ->
      (∃ m:nat, ps(A') = ps(A) ∪ {[m]}) ->
      interpolation_statement A' B
    )
  )
->
  interpolation_statement A B.
Proof.
Admitted.



Theorem interpolation_theorem (A B : prop) :
interpolation_condition A B -> interpolation_statement A B.
Proof.
intros.
remember (size (difference (ps(A)) (ps(B)) )) as n eqn:Heqn.
induction n.
-unfold interpolation_statement. unfold interpolation_condition in H.
admit.
-


apply induction_on_X.

(*having the interpolation condition*)
-apply H.

(*base case of the induction*)
-intro. unfold interpolation_condition in H. unfold interpolation_statement.
destruct H. destruct H. destruct H.
exists A. split. apply taut4. split. apply H1. set_solver.

(*step case of the induction*)
-intros. destruct H1 as [p H1]. unfold interpolation_condition in H.
destruct H. destruct H as [q H]. destruct H. destruct p.

(*defining three new propositions*)
set (A₁ := substitution x A' (Imp (Atom q) (Atom q))).
set (A₂ := substitution x A' (Neg (Imp (Atom q) (Atom q))) ).
set (A₃ := Or A₁ A₂).

unfold interpolation_statement. exists A₃. split.


(* here we need to proof that A' -> A₃, the first condition*)
+ unfold A₃. unfold A₁. unfold A₂. unfold taut. unfold model1. simpl. intro.
  (* getting interpret I A' as an assumption *)
  destruct (interpret I A') eqn:I_A'_state.
  ++simpl. apply orb_true_iff.
      (* destructing p and proving the statement based on the state of p *)
      destruct (I x) eqn:p_state.
      -- left. apply substitution_by_equivalence_props with (p:=Top).
      apply always_true. apply substitution_by_top. assumption. assumption.
      -- right. apply substitution_by_equivalence_props with (p:=Bot).
      apply always_false. apply substitution_by_bot. assumption. assumption.
  ++reflexivity.


+(* first goal is accomplished, two goals left. *) split.

(* now we need to prove that A₃ -> B *)
--unfold taut in H2. unfold model1 in H2.
  assert (A1_imp_B : ⊨₀ Imp A₁ B).
  {
    unfold A₁.
    apply implication_by_equvalence_props with (p := substitution x A' Top).
    -unfold equivalence2. intros. split.
      +apply substitution_by_equivalence_props. apply equiv1.
      +apply substitution_by_equivalence_props. apply equiv_symmetry. apply equiv1.
    -unfold taut. unfold model1. intros. apply validity_preserving1. assumption.
  }
  assert (A2_imp_B : ⊨₀ Imp A₂ B).
  {
    unfold A₃.
    apply implication_by_equvalence_props with (p := substitution x A' Bot).
    -unfold equivalence2. intros. split.
      +apply substitution_by_equivalence_props. apply equiv2.
      +apply substitution_by_equivalence_props. apply equiv_symmetry. apply equiv2.
    -unfold taut. unfold model1. intros. apply validity_preserving2. assumption.
  }
  apply completeness2 in A1_imp_B. apply completeness2 in A2_imp_B.
  unfold A₃. apply soundness2. apply imp_intro. eapply or_elim.
  instantiate (2:= A₁). instantiate (1:= A₂). in_context.
  rewrite set_swap; apply weakening. apply deduction_theorem in A1_imp_B.
  assumption. apply deduction_theorem in A2_imp_B. rewrite set_swap.
  apply weakening. assumption.

(* the last part of the theorem *)
--

Admitted.
