
From stdpp Require Import gmap.
From stdpp Require Import base.
From stdpp Require Import countable strings.


Inductive proposition : Type :=
  | Bot
  | Atom  (n : nat)
  | And   (p1 p2 : proposition)
  | Or    (p1 p2 : proposition)
  | Imp   (p1 p2 : proposition)
  | Neg   (p1 : proposition).

Check Bot.


Fixpoint level (p : proposition) : nat :=
  match p with
  | Bot => 0
  | Atom _ => 0
  | And p1 p2 => if (level p1) <=? (level p2)
  then (level p2) + 1 else (level p1) + 1
  | Or p1 p2 => if (level p1) <=? (level p2)
  then (level p2) + 1 else (level p1) + 1
  | Imp p1 p2 => if (level p1) <=? (level p2)
  then (level p2) + 1 else (level p1) + 1
  | Neg p1 => (level p1) + 1
  end.


Theorem induction_on_level (q : proposition -> Prop) :
  ( forall (A : proposition) , (forall B : proposition, (level B < level A) -> (q B)) -> (q A) ) -> (forall C : proposition , q C) .
Proof.
Admitted.

Check gset.
Check (gset proposition).

Check (EqDecision proposition).
(*
Instance EqDecision_proposition : EqDecision proposition := proposition_eq.
 *)

Global Instance proposition_eq_dec : EqDecision proposition.
Proof.
unfold EqDecision.
unfold Decision.
induction x.
-destruct y.
  + left. reflexivity.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
-destruct y.
  + right. unfold not. intro. inversion H.
  + destruct (n =? n0) eqn:h1.
    ++ apply Nat.eqb_eq in h1. left. rewrite h1. reflexivity.
    ++ apply Nat.eqb_neq in h1. unfold not in h1. right. unfold not.
    intro. inversion H. apply h1 in H1. assumption.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
-destruct y.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + specialize IHx1 with (y := y1). specialize IHx2 with ( y := y2).
    destruct IHx1.
    ++ destruct IHx2.
      --left. rewrite e. rewrite e0. reflexivity.
      --right. unfold not. intro. inversion H. apply n. apply H2.
    ++ destruct IHx2.
      --right. unfold not. intro. inversion H. apply n. apply H1.
      --right. unfold not. intro. inversion H. apply n. apply H1.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
-destruct y.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + specialize IHx1 with (y := y1). specialize IHx2 with ( y := y2).
    destruct IHx1.
    ++ destruct IHx2.
      --left. rewrite e. rewrite e0. reflexivity.
      --right. unfold not. intro. inversion H. apply n. apply H2.
    ++ destruct IHx2.
      --right. unfold not. intro. inversion H. apply n. apply H1.
      --right. unfold not. intro. inversion H. apply n. apply H1.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
-destruct y.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + specialize IHx1 with (y := y1). specialize IHx2 with ( y := y2).
    destruct IHx1.
    ++ destruct IHx2.
      --left. rewrite e. rewrite e0. reflexivity.
      --right. unfold not. intro. inversion H. apply n. apply H2.
    ++ destruct IHx2.
      --right. unfold not. intro. inversion H. apply n. apply H1.
      --right. unfold not. intro. inversion H. apply n. apply H1.
  + right. unfold not. intro. inversion H.
-destruct y.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + right. unfold not. intro. inversion H.
  + specialize IHx with (y := y).
    destruct IHx.
    ++ left. rewrite e. reflexivity.
    ++ right. unfold not. intro. apply n. inversion H. reflexivity.
Qed.




Global Instance proposition_count : Countable proposition.
Proof.
Admitted.



Fixpoint sub_expression (p : proposition) : gset proposition :=
  match p with
  | Bot => {[Bot]}
  | Atom n => {[Atom n]}
  | And p1 p2 => (sub_expresion p1) ∪ (sub_expresion p2) ∪ {[And p1 p2]}
  | Or p1 p2 => (sub_expresion p1) ∪ (sub_expresion p2) ∪ {[Or p1 p2]}
  | Imp p1 p2 => (sub_expresion p1) ∪ (sub_expresion p2) ∪ {[Imp p1 p2]}
  | Neg p1 => (sub_expresion p1) ∪ {[Neg p1]}
  end.

Example sub_expression_example : (Atom 2) ∈ (sub_expresion (And (Neg (Atom 2)) (Atom 1)) ).
Proof.
simpl.
apply elem_of_union. left. apply elem_of_union.
left. apply elem_of_union. left. apply elem_of_singleton. reflexivity.
Qed.



(*
evaluation and interpretation functions,
evaluation assigns a truth value to the atoms,
iterpretation on the other hand, assigns a truth value
to the well formed propositions.
*)

Definition eval_fun := nat -> bool.
Definition myeval : eval_fun :=  fun x : nat => true.

Definition implb (b1 b2 : bool) : bool :=
  if b1 then b2 else true.

Fixpoint interpret : eval_fun -> (proposition -> bool) :=
  fun e p => match p with
  | Bot => false
  | Atom n => e n
  | And p1 p2 => andb (interpret e p1) (interpret e p2)
  | Or p1 p2 => orb (interpret e p1) (interpret e p2)
  | Imp p1 p2 => implb (interpret e p1) (interpret e p2)
  | Neg p1 => negb (interpret e p1)
  end.


Lemma either_true_or_false (I : eval_fun) (p : proposition) :
  {(interpret I p) = true} + {(interpret I p) = false}.
Proof.
destruct (interpret I p).
-left. reflexivity.
-right. reflexivity.
Qed.

Lemma interpret_and (I : eval_fun) (p1 p2 : proposition):
  interpret I (And p1 p2) = true <-> (interpret I p1) ∧ (interpret I p2).
Proof.
Admitted.


Theorem only_atoms_matter :
forall p:proposition, forall e1 e2:eval_fun, (forall n : nat , e1 n = e2 n) -> interpret e1 p = interpret e2 p.
Proof.
intros.
induction p.
-reflexivity.
-simpl. apply H.
-simpl. rewrite IHp1. rewrite IHp2. reflexivity.
-simpl. rewrite IHp1. rewrite IHp2. reflexivity.
-simpl. rewrite IHp1. rewrite IHp2. reflexivity.
-simpl. rewrite IHp. reflexivity.
Qed.


Definition model1 (I: eval_fun) (p : proposition) := interpret I p = true.
Notation "I ⊨₁ p" := (model1 I p) (at level 50).


Example model_example : myeval ⊨₁ (And (Atom 1) (Atom 2)).
Proof.
unfold model1. simpl. unfold myeval. reflexivity.
Qed.


Definition model2 (I: eval_fun) (Γ : gset proposition) :=
  forall p:proposition, p ∈ Γ -> I ⊨₁ p.
Notation "I ⊨₂ Γ" := (model2 I Γ) (at level 50).

Definition model3 (Γ : gset proposition) (p : proposition) :=
  forall I:eval_fun , I ⊨₂ Γ -> I ⊨₁ p.
Notation "Γ ⊨₃ p" := (model3 Γ p) (at level 50).

Example model3_example : {[Atom 1]} ⊨₃ (Atom 1).
Proof.
unfold model3. unfold model2. unfold model1. intros.
specialize H with (p := (Atom 1)). apply H.
apply elem_of_singleton. reflexivity.
Qed.


Example model3_example2 :
  forall A B : proposition, {[A; Imp A B]} ⊨₃ B.
Proof.
intros. unfold model3. unfold model2. unfold model1. intros.
destruct (interpret I B) eqn:h1. reflexivity.
assert (interpret I A = true).
{
  apply H. apply elem_of_union. left. apply elem_of_singleton. reflexivity.
}
assert (interpret I (Imp A B) = true).
{
  apply H. apply elem_of_union. right. apply elem_of_singleton. reflexivity.
}
assert (interpret I (Imp A B) = false).
{
  simpl. rewrite h1. rewrite H0. simpl. reflexivity.
}
rewrite H1 in H2. symmetry. assumption.
Qed.




Definition taut (p : proposition) := forall I:eval_fun , I ⊨₁ p.
Notation "⊨₀ p" := (taut p) (at level 49).

Definition equivalence (p q : proposition) := ⊨₀ And (Imp p q) (Imp q p).
Notation "A ≡ B" := (equivalence A B) (at level 70).

Definition equivalence2 (p q : proposition) :=
  forall I : eval_fun, interpret I p = true <-> interpret I q = true.
Notation "A ≡₂ B" := (equivalence2 A B) (at level 70).


Lemma equive_eq (A B : proposition): (A ≡ B) <-> (A ≡₂ B).
Proof.
unfold equivalence. unfold equivalence2. unfold taut. unfold model1.
split.
-intros. split.
  + intros. simpl in H. specialize H with (I := I). rewrite H0 in H. simpl in H.
  apply andb_prop in H. destruct H. apply H.
  + intros. simpl in H. specialize H with (I := I). rewrite H0 in H. simpl in H.
  apply andb_prop in H. destruct H. apply H1.
- intros. simpl. unfold implb. specialize H with (I := I). destruct (interpret I A) eqn:h1.
  +destruct H. assert (h2 : interpret I B = true). {apply H. reflexivity. }
  rewrite h2. reflexivity.
  +destruct (interpret I B) eqn:h2. inversion H. simpl. apply H1. reflexivity. reflexivity.
Qed.



Example taut1 : ⊨₀ Imp (Atom 0) (Atom 0).
Proof.
unfold taut.
intros. unfold model1. simpl. unfold implb.
destruct (I 0) ; reflexivity.
Qed.

Example taut2 : ⊨₀ Or (Neg (Atom 0)) (Atom 0).
Proof.
unfold taut.
intros. unfold model1. simpl. destruct (I 0). simpl. reflexivity. simpl. reflexivity.
Qed.


Example taut3 :
  forall p : proposition, ⊨₀ Or (Neg p) (p).
Proof.
unfold taut.
intros. unfold model1. simpl. destruct (interpret I p) eqn:h1.
simpl. reflexivity. simpl. reflexivity.
Qed.

Example taut4 :
  forall p : proposition, ⊨₀ Imp p p.
Proof.
unfold taut.
intros. unfold model1. simpl. destruct (interpret I p) eqn:h1.
simpl. reflexivity. simpl. reflexivity.
Qed.


Fixpoint substitution (n : nat) (A B : proposition) : proposition :=
  match A with
  | Bot       => Bot
  | Atom m    => if Nat.eqb m n then B else A
  | And P1 P2 => And (substitution n P1 B) (substitution n P2 B)
  | Or  P1 P2 => Or  (substitution n P1 B) (substitution n P2 B)
  | Imp P1 P2 => Imp (substitution n P1 B) (substitution n P2 B)
  | Neg P1    => Neg (substitution n P1 B)
  end.

Example sub1 : forall (n : nat) (p q A : proposition),
  p ≡ q -> substitution n A p ≡ substitution n A q.
Proof.
intros. apply equive_eq in H. apply equive_eq.
unfold equivalence2 in H. unfold equivalence2.
induction A.
-simpl. reflexivity.
-simpl. destruct (n0 =? n) eqn:h1.
  +apply H.
  +simpl. intro. reflexivity.
-intros. simpl. split.
  + intros. specialize IHA1 with (I := I). specialize IHA2 with (I := I).
   apply andb_true_iff in H0. destruct H0.
   apply andb_true_iff. split. apply IHA1. apply H0. apply IHA2. apply H1.
  + intros. specialize IHA1 with (I := I). specialize IHA2 with (I := I).
   apply andb_true_iff in H0. destruct H0.
   apply andb_true_iff. split. apply IHA1. apply H0. apply IHA2. apply H1.
-intros. simpl. split.
  + intros. specialize IHA1 with (I := I). specialize IHA2 with (I := I).
Admitted.





Example sub2 : forall (p q:nat) (A : proposition),
    {[Atom p]} ⊨₃ A <-> ⊨₀ (substitution p A (Imp (Atom q) (Atom q)) ).
Proof.
intros.
split.
-unfold model3. unfold taut. unfold model2. unfold model1.
intros.
Admitted.


Theorem substitution_tautology :
  forall (n:nat) (A B : proposition), ⊨₀ A -> ⊨₀ substitution n A B.
Proof.
unfold taut. unfold model1. intros. simpl.
induction A.
-simpl. specialize H with (I := I). rewrite <- H. reflexivity.
-simpl. destruct (n0 =? n) eqn:h1.
  + pose (F := fun n => if Nat.eqb n n0 then false else true).
  assert (h2 : interpret F (Atom n0) = false). { simpl. unfold F.
  rewrite (Nat.eqb_refl n0). reflexivity. }
  specialize H with (I := F). rewrite H in h2. inversion h2.
  +specialize H with (I := I). assumption.
-simpl.
Admitted.



(*
implementing the set of proposition symbols
in a well formed formula.
*)

Check ∅.

Fixpoint proposition_symbols (p : proposition) : gset nat :=
  match p with
  | Bot => ∅
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
