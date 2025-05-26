

From stdpp Require Import gmap.
From stdpp Require Import base.
From stdpp Require Import countable strings.

Require Import formulas.
Require Import evaluation.
Require Import substitution.
Require Import deduction.

(*
here we implement a hilbert style proof system,
and we try to proof the completeness theorem for it.
*)

Reserved Notation
  "Γ ⊢ₕ p'"
  (at level 70).

Inductive hilbert_deduction :
  context -> prop -> Prop :=

  (* when a formula belongs to the context, we can prove it. *)
  | h_axiom (Γ : context) (p : prop) :
      p ∈ Γ ->
      Γ ⊢ₕ p

  (* whether we have B or not doesn't matter, we have the A. *)
  | h_weak (Γ : context) (A B : prop) :
      Γ ⊢ₕ Imp A (Imp B A)


  | h_imp_distr (Γ : context) (A B C : prop) :
      Γ ⊢ₕ Imp (Imp A (Imp B C)) (Imp (Imp A B) (Imp A C))


  | h_and_intro (Γ : context) (A B : prop) :
      Γ ⊢ₕ Imp A (Imp B (And A B))


  | h_and_elim_l (Γ : context) (A B : prop) :
      Γ ⊢ₕ Imp (And A B) A


  | h_and_elim_r (Γ : context) (A B : prop) :
      Γ ⊢ₕ Imp (And A B) B


  | h_or_elim (Γ : context) (A B C : prop) :
      Γ ⊢ₕ Imp
      (Imp A B)
      (Imp (Imp C B) (Imp (Or A C) B))


  | h_or_intro_l (Γ : context) (A B : prop) :
      Γ ⊢ₕ Imp A (Or A B)


  | h_or_intro_r (Γ : context) (A B : prop) :
      Γ ⊢ₕ Imp B (Or A B)


  | h_double_neg_elim (Γ : context) (A : prop) :
      Γ ⊢ₕ Imp (Neg (Neg A)) A


  | h_bot_intro (Γ : context) (A : prop) :
      Γ ⊢ₕ Imp (Neg A) (Imp A Bot)


  | h_bot_elim (Γ : context) (A : prop) :
      Γ ⊢ₕ Imp (Imp A Bot) (Neg A)


  | h_top_intro (Γ : context) :
      Γ ⊢ₕ Top


  | h_modus_ponens (Γ : context) (A B : prop) :
      Γ ⊢ₕ A ->
      Γ ⊢ₕ Imp A B ->
      Γ ⊢ₕ B


  where "Γ ⊢ₕ p" := (hilbert_deduction Γ p).


Example hd1 (p q : prop) : {[p ; Imp p q]} ⊢ₕ q.
Proof.
apply h_modus_ponens with (A:=p); apply h_axiom; set_solver.
Qed.



Example hd2 (Γ : context) (A : prop):
  Γ ⊢ₕ Imp A (Imp (Imp A A) A).
Proof.
apply h_weak.
Qed.


Example hd3 (Γ : context) (A B : prop) :
  Γ ⊢ₕ Imp
  (Imp A (Imp B A))
  (Imp (Imp A B) (Imp A A)).
Proof.
apply h_imp_distr.
Qed.

Example hd4 (Γ : context) (A : prop) :
  Γ ⊢ₕ Imp A A.
Proof.
apply h_modus_ponens with (A := Imp A (Imp A A)). apply h_weak.
apply h_modus_ponens with (A := Imp A (Imp (Imp A A) A)).
apply h_weak. apply h_imp_distr.
Qed.


(*
it is used in the next theorem
so you need to prove it later.
*)
Theorem deduction_theorem_hd (Γ : context) (A B : prop):
  Γ ∪ {[A]} ⊢ₕ B <-> Γ ⊢ₕ Imp A B.
Proof.
Admitted.


Theorem nd_eq_hd (Γ : context) (p : prop) :
  (Γ ⊢ p) <-> (Γ ⊢ₕ p).
Proof.
split.
-intros. induction H; subst.
  +apply h_axiom. assumption.
  +eapply h_modus_ponens. apply IHnatural_deduction. apply h_and_elim_l.
  +eapply h_modus_ponens. apply IHnatural_deduction. apply h_and_elim_r.
  +eapply h_modus_ponens. apply IHnatural_deduction2.
  eapply h_modus_ponens. apply IHnatural_deduction1.
  apply h_and_intro.
  +apply h_modus_ponens with (A := Or A B). assumption.
  apply h_modus_ponens with (A := Imp B p).
  apply deduction_theorem_hd in IHnatural_deduction3. assumption.
  apply h_modus_ponens with (A := Imp A p).
  apply deduction_theorem_hd in IHnatural_deduction2. assumption.
  apply h_or_elim.
  +eapply h_modus_ponens. apply IHnatural_deduction. apply h_or_intro_l.
  +eapply h_modus_ponens. apply IHnatural_deduction. apply h_or_intro_r.
  +eapply h_modus_ponens. apply IHnatural_deduction1. assumption.
  +apply deduction_theorem_hd. assumption.
  +apply h_modus_ponens with (A := p). assumption.
  apply h_modus_ponens with (A := Neg p). assumption.
  apply h_bot_intro.
  +apply deduction_theorem_hd in IHnatural_deduction.
  apply h_modus_ponens with (A := Imp p Bot). assumption.
  apply h_bot_elim.
  +apply h_modus_ponens with (A := Neg (Neg p)).
  apply deduction_theorem_hd in IHnatural_deduction.
  apply h_modus_ponens with (A := Imp (Neg p) Bot). assumption.
  apply h_bot_elim. apply h_double_neg_elim.
  +apply h_modus_ponens with (A := Neg (Neg p)).
  apply h_modus_ponens with (A := Imp (Neg p) Bot).
  apply h_modus_ponens with (A := Bot). assumption.
  apply h_weak. apply h_bot_elim. apply h_double_neg_elim.
  +apply h_top_intro.

-intro. induction H; subst.
  +apply axiom. assumption.
  +apply imp_intro. apply imp_intro. apply axiom. set_solver.
  +apply imp_intro. apply imp_intro. apply imp_intro.
  apply imp_elim with (q := B). apply imp_elim with (q := A).
  in_context. in_context. apply imp_elim with (q := A).
  in_context. in_context.
  +apply imp_intro. apply imp_intro. apply and_intro. repeat in_context.
  in_context.
  +apply imp_intro. eapply and_elim_left with (q := B). in_context.
  +apply imp_intro. eapply and_elim_right with (q := A). in_context.
  +repeat (apply imp_intro). eapply or_elim.
  instantiate (1 := C). instantiate (1 := A).
  in_context. apply imp_elim with (q := A). in_context. in_context.
  apply imp_elim with (q := C). in_context. in_context.
  +apply imp_intro. apply or_intro_left. in_context.
  +apply imp_intro. apply or_intro_right. in_context.
  +apply imp_intro. apply RAA. apply neg_elim with (p := Neg A).
  in_context. in_context.
  +apply imp_intro. apply imp_intro. apply neg_elim with (p := A).
  in_context. in_context.
  +apply imp_intro. apply neg_intro. apply imp_elim with (q := A).
  in_context. in_context.
  +apply top_intro.
  +apply imp_elim with (q := A). assumption. assumption.
Qed.



