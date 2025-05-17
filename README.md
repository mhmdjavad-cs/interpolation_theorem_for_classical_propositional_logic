# interpolation_theorem_for_classical_propositional_logic


**Theorem. Let A and B be formulas of classical propositional logic , such that:**<br>

**the interpolation condition**<br>
(i) they share at least one propositional symbol in common.<br>
(ii) A -> B.<br>

For any two such formulas of P,<br>

**the interpolation statement**<br>
there exists a formula C (called the P-interpolant of the formulas A and B) such that:<br>

(iii) A -> C.<br>
(iv) C -> B.<br>
(v) C contains only propositional symbols that occur in both A and B (i.e., only propositional symbols shared by A and B).<br>




------------
**formulas.v** :<br>
defines the basic stuff that we need,
the type "prop" is the type of our classical propositions.

there is also some other usefull stuff in this file, like finding sub-formulas and also creating contexts which are basicly just a set of formulas.


------------
**evaluation.v** :<br>
defines the evaluation machanism for formulas of this logic.


------------
**substition.v** :<br>
defines the act of substituting an atom in a formula with another formula, and also provides some additional lemmas and theorems about this operation.


------------
**deduction.v** :<br>
defines natural deduction system for classical propositional logic and also have some usefull theorems like the deduction theorem, soundness and completeness.


**interpolation.v**<br>
is where the interpolation theorem is implemented using all the stuff that we defined and prove before.
