
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
  (at level 70).

Inductive natural_deduction :
  context -> prop -> Prop :=

  (* when a formula belongs to the context, we can prove it. *)
  | axiom (Γ : context) (p : prop) :
      p ∈ Γ ->
      Γ ⊢ p

  (* left and elimination rule: *)
  | and_elim_left (Γ : context) (p q : prop) :
      Γ ⊢ (And p q) ->
      Γ ⊢ p

  (* right elimination rule: *)
  | and_elim_right (Γ : context) (p q : prop) :
      Γ ⊢ (And q p) ->
      Γ ⊢ p

  (* and introduction rule: *)
  | and_intro (Γ : context) (p q: prop) :
      Γ ⊢ p ->
      Γ ⊢ q ->
      Γ ⊢ (And p q)

  (* or elimination rule: *)
  | or_elim (Γ : context) (p A B : prop) :
      Γ ⊢ (Or A B) ->
      Γ ∪ {[A]} ⊢ p ->
      Γ ∪ {[B]} ⊢ p ->
      Γ ⊢ p

  (* left or introduction rule: *)
  | or_intro_left (Γ : context) (p q : prop) :
      Γ ⊢ p ->
      Γ ⊢ (Or p q)

  (* left or introduction rule: *)
  | or_intro_right (Γ : context) (p q : prop) :
      Γ ⊢ p ->
      Γ ⊢ (Or q p)

  (* implication elimination rule: *)
  | imp_elim (Γ : context) (p q : prop) :
      Γ ⊢ q ->
      Γ ⊢ (Imp q p) ->
      Γ ⊢ p

  (* implication introduction rule: *)
  | imp_intro (Γ : context) (p q : prop):
      Γ ∪ {[q]} ⊢ p ->
      Γ ⊢ (Imp q p)

  (* negation elimination rule: *)
  | neg_elim (Γ : context) (p : prop) :
      Γ ⊢ p ->
      Γ ⊢ (Neg p) ->
      Γ ⊢ Bot

  (* negation introduction rule: *)
  | neg_intro (Γ : context) (p : prop) :
      Γ ∪ {[p]} ⊢ Bot ->
      Γ ⊢ (Neg p)

  (* reducto ad absurdum rule: *)
  | RAA (Γ : context) (p : prop):
      Γ ∪ {[Neg p]} ⊢ Bot ->
      Γ ⊢ p

  (* bot elimination rule: *)
  | bot_elim (Γ : context) (p : prop) :
      Γ ⊢ Bot ->
      Γ ⊢ p

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
intros. apply and_intro...
Qed.

Example nd4 : forall p q : prop, {[p ; Neg p]} ⊢ q.
Proof with auto.
intros.
apply bot_elim. apply neg_elim with (p := p)...
Qed.

Example nd5 (Γ : context) (p : prop) : Γ ⊢ Imp p (Neg (Neg p)).
Proof with auto.
intros. apply imp_intro. apply neg_intro.
apply neg_elim with (p := p)...
Qed.

Example nd6 (Γ : context) (p : prop) : Γ ⊢ Or p (Neg p).
Proof with auto.
intros. apply RAA. apply neg_elim with (p := Or p (Neg p)).
- apply or_intro_right. apply neg_intro.
apply imp_elim with (q := Or p (Neg p)).
  + apply or_intro_left. in_context.
  + apply imp_intro. apply neg_elim with ( p := Or p (Neg p))...
- in_context.
Qed.


(* transitivity of proof *)
Theorem proof_is_transitive (Γ : context) (p q : prop) :
  Γ ⊢ p -> {[p]} ⊢ q -> Γ ⊢ q.
Proof.
Admitted.


Lemma set_swap (Γ : context) (A B : prop) :
  (Γ ∪ {[A]} ∪ {[B]}) = (Γ ∪ {[B]} ∪ {[A]}).
Proof.
intros. set_solver.
Qed.


Theorem weakening (Γ : context) (A B : prop):
  (Γ ⊢ A) -> (Γ ∪ {[B]} ⊢ A).
Proof.
intros.
induction H.
-apply axiom. apply elem_of_union_l. apply H.
-eapply and_elim_left. apply IHnatural_deduction.
-eapply and_elim_right. apply IHnatural_deduction.
-apply and_intro; assumption.
-eapply or_elim with (A := A). apply IHnatural_deduction1. rewrite set_swap; assumption.
rewrite set_swap. assumption.
-apply or_intro_left. assumption.
-apply or_intro_right. assumption.
-eapply imp_elim. apply IHnatural_deduction1. assumption.
-apply imp_intro. rewrite set_swap. assumption.
-eapply neg_elim. apply IHnatural_deduction1. assumption.
-apply neg_intro. rewrite set_swap. assumption.
-apply RAA. rewrite set_swap. assumption.
-apply bot_elim. assumption.
-apply top_intro.
Qed.







Theorem deduction_theorem_semantical (Γ : context) (A B : prop):
  ( (Γ ∪ {[A]}) ⊨₃ B ) -> (Γ ⊨₃ Imp A B).
Proof.
unfold model3. unfold model2. unfold model1.
intros.
simpl.
destruct (interpret I A) eqn:h1.
-simpl. apply H. intros.
apply elem_of_union in H1. destruct H1.
  +apply H0. assumption.
  +apply elem_of_singleton in H1. rewrite H1. assumption.
-reflexivity.
Qed.



(* deduction theorem *)
Theorem deduction_theorem (Γ : context) (A B : prop):
  ((Γ ∪ {[A]}) ⊢ B) <-> Γ ⊢ Imp A B.
Proof.
split.
-intros. apply imp_intro. assumption.
-intros. apply imp_elim with (q:= A).
in_context. apply weakening. apply H.
Qed.

(* the soundness theorems for or deduction system*)

Theorem soundness1 (Γ : context) (p : prop) :
  Γ ⊢ p -> Γ ⊨₃ p.
Proof.
unfold model3. unfold model2. unfold model1.
intros.
induction H.
-apply H0. apply H.
-apply IHnatural_deduction in H0. simpl in H0. apply andb_true_iff in H0. apply H0.
-apply IHnatural_deduction in H0. simpl in H0. apply andb_true_iff in H0. apply H0.
-simpl. apply andb_true_iff. split; auto.
-assert (H3 := H0).
apply IHnatural_deduction1 in H0. simpl in H0. apply orb_true_iff in H0. destruct H0.
  +apply IHnatural_deduction2. intros. apply elem_of_union in H4. destruct H4.
    --apply H3. assumption.
    --apply elem_of_singleton in H4. rewrite H4. assumption.
  +apply IHnatural_deduction3. intros. apply elem_of_union in H4. destruct H4.
    --apply H3. assumption.
    --apply elem_of_singleton in H4. rewrite H4. assumption.
-simpl. apply orb_true_iff. left. auto.
-simpl. apply orb_true_iff. right. auto.
-simpl in IHnatural_deduction2. destruct (interpret I q) eqn:m.
  +simpl in IHnatural_deduction2. apply IHnatural_deduction2. assumption.
  +apply IHnatural_deduction1 in H0. discriminate.
-simpl. destruct (interpret I q) eqn:m.
  +simpl. apply IHnatural_deduction. intros. apply elem_of_union in H1. destruct H1.
    --auto.
    --apply elem_of_singleton in H1. rewrite H1. auto.
  +simpl. reflexivity.
-assert (H3 := H0). apply IHnatural_deduction1 in H0. apply IHnatural_deduction2 in H3.
simpl in H3. rewrite H0 in H3. discriminate.
-simpl. simpl in IHnatural_deduction. destruct (interpret I p) eqn:m.
  +simpl. apply IHnatural_deduction. intros. apply elem_of_union in H1. destruct H1.
    --auto.
    --apply elem_of_singleton in H1. rewrite H1. auto.
  +reflexivity.
-destruct (interpret I p) eqn:m. reflexivity. simpl in IHnatural_deduction.
apply IHnatural_deduction. intros. apply elem_of_union in H1. destruct H1.
  +auto.
  +apply elem_of_singleton in H1. rewrite H1. simpl. rewrite m. reflexivity.
-destruct (interpret I p) eqn:m. reflexivity. simpl in IHnatural_deduction. apply IHnatural_deduction.
intros. apply H0. assumption.
-reflexivity.
Qed.


Theorem soundness2 (p : prop) :
  ∅ ⊢ p -> ⊨₀ p.
Proof.
unfold taut. unfold model1. intros.
apply soundness1 in H. unfold model3 in H. unfold model2 in H.
unfold model1 in H. specialize H with (I:=I). apply H.
intros. inversion H0.
Qed.



Lemma union_with_empty (B : prop):
  (∅ : context ) ∪ {[B]} = {[B]}.
Proof.
  set_solver.
Qed.

Lemma union_with_empty2 (Γ : context):
  Γ ∪ ∅ = Γ.
Proof.
set_solver.
Qed.
