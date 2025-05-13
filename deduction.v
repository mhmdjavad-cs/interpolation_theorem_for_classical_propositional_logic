
From stdpp Require Import gmap.
From stdpp Require Import base.
From stdpp Require Import countable strings.

Require Import formulas.
Require Import evaluation.
Require Import substitution.

(*
in this file we are trying to implement
the natural deduction system, and
we will accept soundness and completeness
theorems for it as an axiom.
*)

Inductive natural_deduction :
  (gset proposition) -> (proposition) -> Prop :=
  | axiom (Γ : gset proposition) (p : proposition) :
      p ∈ Γ -> natural_deduction Γ p
  | and_elimination_left (Γ : gset proposition) (p : proposition) :
      (exists q: proposition, natural_deduction Γ (And p q) ) -> natural_deduction Γ p
  | and_elimination_right (Γ : gset proposition) (p : proposition) :
      (exists q: proposition, natural_deduction Γ (And q p) ) -> natural_deduction Γ p
  | and_introduction (Γ : gset proposition) (p q: proposition) :
      (natural_deduction Γ p) ∧ (natural_deduction Γ q) -> natural_deduction Γ (And p q)
  | or_elimination (Γ : gset proposition) (p : proposition) :
      (exists A B : proposition,
      (natural_deduction Γ (Or A B)) ∧
      (natural_deduction (Γ ∪ {[A]}) p) ∧
      (natural_deduction (Γ ∪ {[B]}) p) ) -> natural_deduction Γ p
  | or_introduction_left (Γ : gset proposition) (A B : proposition) :
      (natural_deduction Γ A) -> (natural_deduction Γ (Or A B))
  | or_introduction_right (Γ : gset proposition) (A B : proposition) :
      (natural_deduction Γ B) -> (natural_deduction Γ (Or A B))
  | implication_elimination (Γ : gset proposition) (p : proposition) :
      (exists q : proposition,
      (natural_deduction Γ q) ∧
      (natural_deduction Γ (Imp q p))) -> (natural_deduction Γ p)
  | implication_introduction (Γ : gset proposition) (p q : proposition):
      (natural_deduction (Γ ∪ {[p]}) q) -> (natural_deduction Γ (Imp p q))
  | negation_elimination (Γ : gset proposition) :
      (exists p : proposition,
      (natural_deduction Γ p) ∧ (natural_deduction Γ (Neg p))) ->
      (natural_deduction Γ Bot)
  | negation_introduction (Γ : gset proposition) (p : proposition) :
      (natural_deduction (Γ ∪ {[p]}) Bot) -> (natural_deduction Γ (Neg p))
  | RAA (Γ : gset proposition) (p : proposition):
      (natural_deduction (Γ ∪ {[Neg p]}) Bot) -> (natural_deduction Γ p)
  | bot_elimination (Γ : gset proposition) (p : proposition) :
      (natural_deduction Γ Bot) -> (natural_deduction Γ p)
  | top_introduction (Γ : gset proposition) :
      (natural_deduction Γ Top).


Notation "Γ ⊢ p" :=
  (natural_deduction Γ p)
  (at level 45, no associativity).

Example nd1 : forall p:proposition , {[p]} ⊢ p .
Proof.
intro. apply axiom. set_solver.
Qed.

Example nd2 : forall p q : proposition, {[And p q]} ⊢ p.
Proof.
intros. apply and_elimination_left. exists q.
apply axiom. set_solver.
Qed.

Example nd3 : forall p q : proposition, {[p ; q]} ⊢ (And p q).
Proof.
intros. apply and_introduction. split; apply axiom ; set_solver.
Qed.

Example nd4 : forall p q : proposition, {[p ; Neg p]} ⊢ q.
Proof.
intros.
apply bot_elimination. apply negation_elimination.
exists p. split ; apply axiom ; set_solver.
Qed.

Example nd5 : forall p : proposition, ∅ ⊢ Imp p (Neg (Neg p)).
Proof.
intros. apply implication_introduction. apply negation_introduction.
apply negation_elimination. exists p. split; apply axiom; set_solver.
Qed.

Example nd6 : forall p : proposition, ∅ ⊢ Or p (Neg p).
Proof.
intros. apply RAA. apply negation_elimination.
exists (Or p (Neg p)). split.
- apply or_introduction_right. apply negation_introduction.
apply implication_elimination. exists (Or p (Neg p)). split.
  + apply or_introduction_left. apply axiom. set_solver.
  + apply implication_introduction. apply negation_elimination.
  exists (Or p (Neg p)). split; apply axiom ; set_solver.
- apply axiom ; set_solver.
Qed.


(* transitivity of proof *)

Theorem proof_is_transitive (Γ : gset proposition) (p q : proposition) :
  Γ ⊢ p -> {[p]} ⊢ q -> Γ ⊢ q.
Proof.
Admitted.



(* deduction theorem *)

Theorem deduction_theorem (Γ : gset proposition) (A B : proposition):
  ((Γ ∪ {[A]}) ⊢ B) <-> Γ ⊢ Imp A B.
Proof.
Admitted.




(* the soundness theorems for or deduction system*)

Theorem soundness1 (Γ : gset proposition) (p : proposition) :
  Γ ⊢ p -> Γ ⊨₃ p.
Proof.
unfold model3. unfold model2. unfold model1.
intros.
Admitted.

Theorem soundness2 (p : proposition) :
  ∅ ⊢ p -> ⊨₀ p.
Proof.
unfold taut. unfold model1. intros.
apply soundness1 in H. unfold model3 in H. unfold model2 in H.
unfold model1 in H. specialize H with (I:=I). apply H.
intros. inversion H0.
Qed.
