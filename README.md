# interpolation_theorem_for_classical_propositional_logic


Theorem. Let A and B be formulas of P , such that (1) they share at least one propositional symbol in com- mon, and (2) îP A ⊃ B. For any two such formulas of P, there exists a formula C (called the P-interpolant of the formulas A and B) such that (3) îP A ⊃ C, (4) îP C ⊃ B, and (5) C contains only propositional symbols that occur in both A and B (i.e., only propositional symbols shared by A and B).


------------
formulas.v :
defines the basic stuff that we need,
the type "prop" is the type of our classical propositions.

there is also some other usefull stuff in this file, like finding sub-formulas and also creating contexts which are basicly just a set of formulas.


------------
evaluation.v :
defines the evaluation machanism for formulas of this logic.


------------
substition.v :
defines the act of substituting an atom in a formula with another formula, and also provides some additional lemmas and theorems about this operation.


------------
deduction.v :
defines natural deduction system for classical propositional logic and also have some usefull theorems like the deduction theorem, soundness and completeness.


** interpolation.v **
is where the interpolation theorem is implemented using all the stuff that we defined and prove before.

