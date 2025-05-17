
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




Reserved Notation
  "Γ ⊢ p'"
  (at level 40).

Inductive natural_deduction :
  context -> prop -> Prop :=

  (* when a formula belongs to the context, we can prove it. *)
  | axiom (Γ : context) (p : prop) :
      p ∈ Γ -> Γ ⊢ p

  (* left and elimination rule: *)
  | and_elim_left (Γ : context) (p q : prop) :
      ( Γ ⊢ (And p q) ) -> Γ ⊢ p

  (* right elimination rule: *)
  | and_elim_right (Γ : context) (p q : prop) :
       Γ ⊢ (And q p)  -> Γ ⊢ p

  (* and introduction rule: *)
  | and_intro (Γ : context) (p q: prop) :
      (Γ ⊢ p) ∧ (Γ ⊢ q) -> Γ ⊢ (And p q)

  (* or elimination rule: *)
  | or_elim (Γ : context) (p A B : prop) :
      ( Γ ⊢ (Or A B) ∧
      (Γ ∪ {[A]}) ⊢ p ∧
      (Γ ∪ {[B]}) ⊢ p)
      -> (Γ ⊢ p)

  (* left or introduction rule: *)
  | or_intro_left (Γ : context) (p q : prop) :
      (Γ ⊢ p) -> (Γ ⊢ (Or p q))

  (* left or introduction rule: *)
  | or_intro_right (Γ : context) (p q : prop) :
      (Γ ⊢ p) -> (Γ ⊢ (Or q p))

  (* implication elimination rule: *)
  | imp_elim (Γ : context) (p q : prop) :
      (Γ ⊢ q) ∧ (Γ ⊢ (Imp q p)) -> (Γ ⊢ p)

  (* implication introduction rule: *)
  | imp_intro (Γ : context) (p q : prop):
      ((Γ ∪ {[q]}) ⊢ p) -> (Γ ⊢ (Imp q p))

  (* negation elimination rule: *)
  | neg_elim (Γ : context) (p : prop) :
      (Γ ⊢ p) ∧ (Γ ⊢ (Neg p)) ->
      (Γ ⊢ Bot)

  (* negation introduction rule: *)
  | neg_intro (Γ : context) (p : prop) :
      ((Γ ∪ {[p]}) ⊢ Bot) -> (Γ ⊢ (Neg p))

  (* reducto ad absurdum rule: *)
  | RAA (Γ : context) (p : prop):
      ((Γ ∪ {[Neg p]}) ⊢ Bot) -> (Γ ⊢ p)

  (* bot elimination rule: *)
  | bot_elim (Γ : context) (p : prop) :
      (Γ ⊢ Bot) -> (Γ ⊢ p)

  (* top introduction rule: *)
  | top_intro (Γ : context) :
      Γ ⊢ Top

  where "Γ ⊢ p" := (natural_deduction Γ p).

(* Notation "Γ ⊢ p" :=
  (natural_deduction Γ p)
  (at level 45, no associativity). *)

Example nd1 : forall p:prop , {[p]} ⊢ p .
Proof.
intro. apply axiom. set_solver.
Qed.

Ltac in_context :=
  intros; apply axiom; set_solver.

Hint Constructors natural_deduction : core.
Hint Extern 1 (_ ⊢ _) => in_context : core.


Example nd1' : forall p : prop , {[p]} ⊢ p.
Proof with in_context.
intro...
Qed.

Example nd1'' : forall p : prop , {[p]} ⊢ p.
Proof.
auto.
Qed.


Example nd2 : forall p q : prop, {[And p q]} ⊢ p.
Proof with auto.
intros.
apply and_elim_left with (q := q)...
Qed.

Example nd3 : forall p q : prop, {[p ; q]} ⊢ (And p q).
Proof with auto.
intros. apply and_intro. split...
Qed.

Example nd4 : forall p q : prop, {[p ; Neg p]} ⊢ q.
Proof with auto.
intros.
apply bot_elim. apply neg_elim with (p := p).
split...
Qed.

Example nd5 : forall p : prop, ∅ ⊢ Imp p (Neg (Neg p)).
Proof with auto.
intros. apply imp_intro. apply neg_intro.
apply neg_elim with (p := p). split...
Qed.

Example nd6 : forall p : prop, ∅ ⊢ Or p (Neg p).
Proof with auto.
intros. apply RAA. apply neg_elim with (p := Or p (Neg p)). split.
- apply or_intro_right. apply neg_intro.
apply imp_elim with (q := Or p (Neg p)). split.
  + apply or_intro_left. in_context.
  + apply imp_intro. apply neg_elim with ( p := Or p (Neg p)). split...
- in_context.
Qed.


(* transitivity of proof *)
Theorem proof_is_transitive (Γ : context) (p q : prop) :
  Γ ⊢ p -> {[p]} ⊢ q -> Γ ⊢ q.
Proof.
intros.
inversion H.
-inversion H0.
  +apply elem_of_singleton in H4. rewrite <- H4 in H1.
  apply axiom. assumption.
  +
  Admitted.



(* deduction theorem *)
Theorem deduction_theorem (Γ : context) (A B : prop):
  ((Γ ∪ {[A]}) ⊢ B) <-> Γ ⊢ Imp A B.
Proof.
split.
-intros. apply imp_intro. assumption.
-intros. inversion H.
  +apply imp_elim with (q:=A). split. in_context. apply axiom.
  apply elem_of_union. left. assumption.
  +
  Admitted.





(* the soundness theorems for or deduction system*)

Theorem soundness1 (Γ : context) (p : prop) :
  Γ ⊢ p -> Γ ⊨₃ p.
Proof.
unfold model3. unfold model2. unfold model1.
intros.
Admitted.

Theorem soundness2 (p : prop) :
  ∅ ⊢ p -> ⊨₀ p.
Proof.
unfold taut. unfold model1. intros.
apply soundness1 in H. unfold model3 in H. unfold model2 in H.
unfold model1 in H. specialize H with (I:=I). apply H.
intros. inversion H0.
Qed.


(* completeness theorems for our proof system *)
Theorem completeness1 (Γ : context) (q : prop) :
  (Γ ⊨₃ q) -> (Γ ⊢ q).
Proof.
unfold model3. unfold model2. unfold model1.
intros.
Admitted.

Theorem completeness2 (q : prop) :
  (⊨₀ q) -> (∅ ⊢ q).
Proof.
unfold taut. unfold model1.
intros.
apply completeness1. unfold model3. unfold model2. unfold model1.
intros. apply H.
Qed.


Lemma union_with_empty (B : prop):
  (∅ : context ) ∪ {[B]} = {[B]}.
Proof.
  set_solver.
Qed.


Example implication_is_transitive (A B C : prop) :
  (⊨₀ Imp A B) ->
  (⊨₀ Imp B C) ->
  (⊨₀ Imp A C).
Proof.
intros.
apply soundness2.
apply completeness2 in H.
apply completeness2 in H0.
apply imp_intro.
eapply proof_is_transitive.
-apply deduction_theorem in H.
instantiate (1 := B). assumption.
-apply deduction_theorem in H0. rewrite union_with_empty in H0. assumption.
Qed.
