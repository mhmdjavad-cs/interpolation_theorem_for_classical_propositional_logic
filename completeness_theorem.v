
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
Require Import propositional_symbols.

(*
this file contains the proof of completeness1
and completeness2 theorems, some theorems about sets
and proof of the transitivity of proofs.
*)


Fixpoint ps' (A : prop) (I : eval_fun) : context :=
  match A with
  | Bot       => ∅
  | Top       => ∅
  | Atom n    => if I n then {[Atom n]} else {[Neg (Atom n)]}
  | And p1 p2 => (ps' p1 I) ∪ (ps' p2 I)
  | Or  p1 p2 => (ps' p1 I) ∪ (ps' p2 I)
  | Imp p1 p2 => (ps' p1 I) ∪ (ps' p2 I)
  | Neg p1    => (ps' p1 I)
  end.


Example ps'1 : ps' (And (Atom 1) (Neg (Atom 2))) myeval = {[Atom 1; Atom 2]}.
Proof.
simpl.
set_solver.
Qed.



Definition invert_prop (A : prop) (I : eval_fun) : prop :=
  if interpret I A then A else Neg (A).




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


Lemma union_assoc (A B C : context) :
  A ∪ (B ∪ C) = (A ∪ B) ∪ C.
Proof. set_solver. Qed.

Lemma union_symm (A B : context) :
  A ∪ B = B ∪ A.
Proof. set_solver. Qed.



Theorem weakening2 (Γ Γ' : context) (A : prop):
  (Γ ⊢ A) -> (Γ ∪ Γ' ⊢ A).
Proof.
remember (size ( Γ' )) as n eqn:Heqn.
generalize dependent Γ'.
generalize dependent Γ.
generalize dependent A.
induction n.
-intros. symmetry in Heqn. apply card_zero_eq_empty in Heqn.
rewrite Heqn. rewrite union_with_empty2. assumption.
-intros.
pose proof Heqn as h1. symmetry in h1.
apply one_element in h1. destruct h1.
pose proof H0 as h1. apply getting_one_element in h1.
destruct h1. destruct H1.
rewrite <- H1. rewrite union_assoc.
assert (H3 : Γ ∪ x0 ⊢ A).
{
  apply IHn. rewrite H2. rewrite <- Heqn. simpl. rewrite Nat.sub_0_r.
  reflexivity. assumption.
}
apply weakening. assumption.
Qed.




(* main lemma *)
Lemma main_lemma (A : prop) (I : eval_fun) :
  ps' A I ⊢ₕ invert_prop A I.
Proof.
unfold invert_prop.
apply nd_eq_hd.
induction A.
-simpl. apply neg_intro. in_context.
-simpl. apply top_intro.
-simpl. destruct (I n) eqn:h1; in_context.
-simpl. eapply weakening2 in IHA1. instantiate (1 := ps' A2 I) in IHA1.
eapply weakening2 in IHA2. instantiate (1 := ps' A1 I) in IHA2.
rewrite union_symm in IHA2. destruct (interpret I A1) eqn:h1.
  +destruct (interpret I A2) eqn:h2.
    --simpl. apply and_intro. assumption. assumption.
    --simpl. apply neg_intro. apply neg_elim with (p:= A2).
    apply and_elim_right with (q:= A1). in_context.
    apply weakening. assumption.
  +destruct (interpret I A2) eqn:h2.
    --simpl. apply neg_intro. apply neg_elim with (p := A1).
    apply and_elim_left with (q:= A2). in_context.
    apply weakening. assumption.
    --simpl. apply neg_intro. apply neg_elim with (p := A1).
    apply and_elim_left with (q:= A2). in_context.
    apply weakening. assumption.
-simpl. eapply weakening2 in IHA1. instantiate (1 := ps' A2 I) in IHA1.
eapply weakening2 in IHA2. instantiate (1 := ps' A1 I) in IHA2.
rewrite union_symm in IHA2. destruct (interpret I A1) eqn:h1.
  +destruct (interpret I A2) eqn:h2.
    --simpl. apply or_intro_left. assumption.
    --simpl. apply or_intro_left. assumption.
  +destruct (interpret I A2) eqn:h2.
    --simpl. apply or_intro_right. assumption.
    --simpl. apply neg_intro. eapply or_elim.
    instantiate (1 := A2). instantiate (1 := A1).
    in_context. apply neg_elim with (p := A1).
    in_context. apply weakening. apply weakening. assumption.
    apply neg_elim with (p := A2).
    in_context. apply weakening. apply weakening. assumption.
-simpl. eapply weakening2 in IHA1. instantiate (1 := ps' A2 I) in IHA1.
eapply weakening2 in IHA2. instantiate (1 := ps' A1 I) in IHA2.
rewrite union_symm in IHA2. destruct (interpret I A1) eqn:h1.
  +destruct (interpret I A2) eqn:h2.
    --simpl. apply imp_intro. apply weakening. assumption.
    --simpl. apply neg_intro. apply neg_elim with (p := A2).
    apply imp_elim with (q := A1). apply weakening. assumption.
    in_context. apply weakening. assumption.
  +destruct (interpret I A2) eqn:h2.
    --simpl. apply imp_intro. apply weakening. assumption.
    --simpl.
    apply imp_intro.
  assert ( ps' A1 I ∪ ps' A2 I ∪ {[A1]} ⊢ A1) as H_A1. {
    apply axiom. set_solver. }
  assert ( ps' A1 I ∪ ps' A2 I ∪ {[A1]} ⊢ Neg A1) as H_negA1. {
    apply weakening. apply IHA1. }
  assert ( ps' A1 I ∪ ps' A2 I ∪ {[A1]} ⊢ Bot) as H_bot. {
    apply neg_elim with (p := A1).
    - apply H_A1.
    - apply H_negA1.
  }
  apply bot_elim with (p := A2).
  apply H_bot.

-simpl. destruct (interpret I A) eqn:h1.
  +simpl. apply imp_elim with (q := A). assumption.
  apply nd5.
  +simpl. assumption.
Qed.











(* completeness theorems for our proof system *)
Theorem completeness1 (q : prop) :
  (⊨₀ q) -> (∅ ⊢ q).
Proof.
Admitted.




(* completeness when context is not empty *)
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
