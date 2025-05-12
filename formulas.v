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
  | And p1 p2 => (sub_expression p1) ∪ (sub_expression p2) ∪ {[And p1 p2]}
  | Or p1 p2 => (sub_expression p1) ∪ (sub_expression p2) ∪ {[Or p1 p2]}
  | Imp p1 p2 => (sub_expression p1) ∪ (sub_expression p2) ∪ {[Imp p1 p2]}
  | Neg p1 => (sub_expression p1) ∪ {[Neg p1]}
  end.

Example sub_expression_example : (Atom 2) ∈ (sub_expression (And (Neg (Atom 2)) (Atom 1)) ).
Proof.
simpl.
apply elem_of_union. left. apply elem_of_union.
left. apply elem_of_union. left. apply elem_of_singleton. reflexivity.
Qed.
