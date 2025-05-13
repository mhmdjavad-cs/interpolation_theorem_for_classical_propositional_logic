
From stdpp Require Import gmap.
From stdpp Require Import base.
From stdpp Require Import countable strings.
From Coq Require Import Bool.


Require Import formulas.
Require Import evaluation.
Require Import substitution.
Require Import propositional_symbols.
Require Import deduction.



(* a theorem for help *)


Theorem substitution_by_top (A : proposition) (p : nat) :
  forall I : eval_fun,
    (I p = true) ->
    ( (interpret I A = true) <-> (interpret I (substitution p A Top) = true)).
Proof.
intros.
induction A.
-simpl. reflexivity.
-simpl. reflexivity.
-simpl. destruct (n =? p) eqn:h1.
  +simpl. split. reflexivity. intro. apply Nat.eqb_eq in h1. rewrite h1. assumption.
  +simpl. reflexivity.
-simpl. destruct (interpret I A1, interpret I A2) as [ [|] [|] ] eqn:h1.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA1 in H1. apply IHA2 in H0. rewrite H0. rewrite H1. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA1 in H1. assert (H3 : interpret I (substitution p A2 Top) = false).
  { destruct (interpret I (substitution p A2 Top)) eqn:m2.
  rewrite <- H0. destruct IHA2. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H1. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA2 in H0.
  assert (H3 : interpret I (substitution p A1 Top) = false).
  { destruct (interpret I (substitution p A1 Top)) eqn:m2.
  rewrite <- H1. destruct IHA1. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H0. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  assert (H3 : interpret I (substitution p A1 Top) = false).
  { destruct (interpret I (substitution p A1 Top)) eqn:m2.
  rewrite <- H1. destruct IHA1. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  assert (H4 : interpret I (substitution p A2 Top) = false).
  { destruct (interpret I (substitution p A2 Top)) eqn:m2.
  rewrite <- H0. destruct IHA2. rewrite <- H4. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H4. reflexivity.
-simpl. destruct (interpret I A1, interpret I A2) as [ [|] [|] ] eqn:h1.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA1 in H1. apply IHA2 in H0. rewrite H0. rewrite H1. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA1 in H1. assert (H3 : interpret I (substitution p A2 Top) = false).
  { destruct (interpret I (substitution p A2 Top)) eqn:m2.
  rewrite <- H0. destruct IHA2. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H1. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA2 in H0.
  assert (H3 : interpret I (substitution p A1 Top) = false).
  { destruct (interpret I (substitution p A1 Top)) eqn:m2.
  rewrite <- H1. destruct IHA1. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H0. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  assert (H3 : interpret I (substitution p A1 Top) = false).
  { destruct (interpret I (substitution p A1 Top)) eqn:m2.
  rewrite <- H1. destruct IHA1. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  assert (H4 : interpret I (substitution p A2 Top) = false).
  { destruct (interpret I (substitution p A2 Top)) eqn:m2.
  rewrite <- H0. destruct IHA2. rewrite <- H4. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H4. reflexivity.
-simpl. destruct (interpret I A1, interpret I A2) as [ [|] [|] ] eqn:h1.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA1 in H1. apply IHA2 in H0. rewrite H0. rewrite H1. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA1 in H1. assert (H3 : interpret I (substitution p A2 Top) = false).
  { destruct (interpret I (substitution p A2 Top)) eqn:m2.
  rewrite <- H0. destruct IHA2. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H1. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA2 in H0.
  assert (H3 : interpret I (substitution p A1 Top) = false).
  { destruct (interpret I (substitution p A1 Top)) eqn:m2.
  rewrite <- H1. destruct IHA1. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H0. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  assert (H3 : interpret I (substitution p A1 Top) = false).
  { destruct (interpret I (substitution p A1 Top)) eqn:m2.
  rewrite <- H1. destruct IHA1. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  assert (H4 : interpret I (substitution p A2 Top) = false).
  { destruct (interpret I (substitution p A2 Top)) eqn:m2.
  rewrite <- H0. destruct IHA2. rewrite <- H4. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H4. reflexivity.
-simpl. destruct (interpret I A) eqn:h1.
  +destruct IHA. rewrite H0. reflexivity. reflexivity.
  +assert (H3 : interpret I (substitution p A Top) = false).
  { destruct (interpret I (substitution p A Top)) eqn:m2. inversion IHA. symmetry. apply H1. reflexivity. reflexivity. }
  rewrite <- H3. reflexivity.
Qed.


Theorem substitution_by_bot (A : proposition) (p : nat) :
  forall I : eval_fun,
    (I p = false) ->
    ( (interpret I A = true) <-> (interpret I (substitution p A Bot) = true)).
Proof.
intros.
induction A.
-simpl. reflexivity.
-simpl. reflexivity.
-simpl. destruct (n =? p) eqn:h1.
  +simpl. split. intro. apply Nat.eqb_eq in h1. rewrite <- H. rewrite <- H0. rewrite h1. reflexivity. intro. inversion H0.
  +simpl. reflexivity.
-simpl. destruct (interpret I A1, interpret I A2) as [ [|] [|] ] eqn:h1.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA1 in H1. apply IHA2 in H0. rewrite H0. rewrite H1. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA1 in H1. assert (H3 : interpret I (substitution p A2 Bot) = false).
  { destruct (interpret I (substitution p A2 Bot)) eqn:m2.
  rewrite <- H0. destruct IHA2. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H1. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA2 in H0.
  assert (H3 : interpret I (substitution p A1 Bot) = false).
  { destruct (interpret I (substitution p A1 Bot)) eqn:m2.
  rewrite <- H1. destruct IHA1. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H0. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  assert (H3 : interpret I (substitution p A1 Bot) = false).
  { destruct (interpret I (substitution p A1 Bot)) eqn:m2.
  rewrite <- H1. destruct IHA1. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  assert (H4 : interpret I (substitution p A2 Bot) = false).
  { destruct (interpret I (substitution p A2 Bot)) eqn:m2.
  rewrite <- H0. destruct IHA2. rewrite <- H4. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H4. reflexivity.
-simpl. destruct (interpret I A1, interpret I A2) as [ [|] [|] ] eqn:h1.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA1 in H1. apply IHA2 in H0. rewrite H0. rewrite H1. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA1 in H1. assert (H3 : interpret I (substitution p A2 Bot) = false).
  { destruct (interpret I (substitution p A2 Bot)) eqn:m2.
  rewrite <- H0. destruct IHA2. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H1. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA2 in H0.
  assert (H3 : interpret I (substitution p A1 Bot) = false).
  { destruct (interpret I (substitution p A1 Bot)) eqn:m2.
  rewrite <- H1. destruct IHA1. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H0. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  assert (H3 : interpret I (substitution p A1 Bot) = false).
  { destruct (interpret I (substitution p A1 Bot)) eqn:m2.
  rewrite <- H1. destruct IHA1. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  assert (H4 : interpret I (substitution p A2 Bot) = false).
  { destruct (interpret I (substitution p A2 Bot)) eqn:m2.
  rewrite <- H0. destruct IHA2. rewrite <- H4. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H4. reflexivity.
-simpl. destruct (interpret I A1, interpret I A2) as [ [|] [|] ] eqn:h1.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA1 in H1. apply IHA2 in H0. rewrite H0. rewrite H1. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA1 in H1. assert (H3 : interpret I (substitution p A2 Bot) = false).
  { destruct (interpret I (substitution p A2 Bot)) eqn:m2.
  rewrite <- H0. destruct IHA2. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H1. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  apply IHA2 in H0.
  assert (H3 : interpret I (substitution p A1 Bot) = false).
  { destruct (interpret I (substitution p A1 Bot)) eqn:m2.
  rewrite <- H1. destruct IHA1. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H0. reflexivity.
  +injection h1. intros. rewrite H0. rewrite H1.
  assert (H3 : interpret I (substitution p A1 Bot) = false).
  { destruct (interpret I (substitution p A1 Bot)) eqn:m2.
  rewrite <- H1. destruct IHA1. rewrite <- H3. reflexivity. reflexivity. reflexivity. }
  assert (H4 : interpret I (substitution p A2 Bot) = false).
  { destruct (interpret I (substitution p A2 Bot)) eqn:m2.
  rewrite <- H0. destruct IHA2. rewrite <- H4. reflexivity. reflexivity. reflexivity. }
  rewrite H3. rewrite H4. reflexivity.
-simpl. destruct (interpret I A) eqn:h1.
  +destruct IHA. rewrite H0. reflexivity. reflexivity.
  +assert (H3 : interpret I (substitution p A Bot) = false).
  { destruct (interpret I (substitution p A Bot)) eqn:m2. inversion IHA. symmetry. apply H1. reflexivity. reflexivity. }
  rewrite <- H3. reflexivity.
Qed.






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


(* here we need to proof that A' -> A₃, the first condition*)
+ unfold A₃. unfold A₁. unfold A₂. unfold taut. unfold model1. simpl. intro.
  (* getting interpret I A' as an assumption *)
  destruct (interpret I A') eqn:I_A'_state.
  ++simpl. Search (_ || _ ). apply orb_true_iff.
      (* destructing p and proving the statement based on the state of p *)
      destruct (I p) eqn:p_state.
      -- left. apply substitution_by_equivalence_props with (p:=Top).
      apply always_true. apply substitution_by_top. assumption. assumption.
      -- right. apply substitution_by_equivalence_props with (p:=Bot).
      apply always_false. apply substitution_by_bot. assumption. assumption.
  ++reflexivity.






Qed.
