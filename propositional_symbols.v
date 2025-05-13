
From stdpp Require Import gmap.
From stdpp Require Import base.
From stdpp Require Import countable strings.

Require Import formulas.
Require Import evaluation.
Require Import substitution.


Fixpoint proposition_symbols (p : proposition) : gset nat :=
  match p with
  | Bot => ∅
  | Top => ∅
  | Atom n => {[n]}
  | And p1 p2 => (proposition_symbols p1) ∪ (proposition_symbols p2)
  | Or p1 p2 => (proposition_symbols p1) ∪ (proposition_symbols p2)
  | Imp p1 p2 => (proposition_symbols p1) ∪ (proposition_symbols p2)
  | Neg p1 => (proposition_symbols p1)
  end.


Notation "ps( p )" :=
  (proposition_symbols p)
  (at level 48, no associativity).


Example ps1 : ps(And (Atom 1) (Atom 2)) = {[1;2]}.
Proof.
simpl. reflexivity.
Qed.


Lemma only_atoms_in_formula_matter :
  forall (p : proposition) (e1 e2 : eval_fun),
    (forall x:nat , x ∈ ps(p) -> e1 x = e2 x) -> interpret e1 p = interpret e2 p.
Proof.
intros.
induction p.
-reflexivity.
-reflexivity.
-simpl. specialize H with (x := n). simpl in H. apply H. set_solver.
-simpl. simpl in H.
assert (H1 : interpret e1 p1 = interpret e2 p1).
{ apply IHp1. intros. specialize H with (x := x). apply H. set_solver. }
assert (H2 : interpret e1 p2 = interpret e2 p2).
{ apply IHp2. intros. specialize H with (x := x). apply H. set_solver. }
rewrite H1. rewrite H2. reflexivity.
-simpl. simpl in H.
assert (H1 : interpret e1 p1 = interpret e2 p1).
{ apply IHp1. intros. specialize H with (x := x). apply H. set_solver. }
assert (H2 : interpret e1 p2 = interpret e2 p2).
{ apply IHp2. intros. specialize H with (x := x). apply H. set_solver. }
rewrite H1. rewrite H2. reflexivity.
-simpl. simpl in H.
assert (H1 : interpret e1 p1 = interpret e2 p1).
{ apply IHp1. intros. specialize H with (x := x). apply H. set_solver. }
assert (H2 : interpret e1 p2 = interpret e2 p2).
{ apply IHp2. intros. specialize H with (x := x). apply H. set_solver. }
rewrite H1. rewrite H2. reflexivity.
-simpl. simpl in H.
assert (H1 : interpret e1 p = interpret e2 p).
{ apply IHp. intros. specialize H with (x := x). apply H. set_solver. }
rewrite H1. reflexivity.
Qed.
