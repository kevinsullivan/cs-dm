***************
Predicate Logic
***************

In this chapter we move from propositional to first-order predicate logic.
First-order predicate logic is the logic of Dafny. Predicate logic is much
more expressive than propositional logic, which as we've seen is isomorphic
to Boolean expressions that include Boolean variables.

Key changes include:

* Variables now range over arbitrary sets; an interpretation specifies the sets over which the variables in a predicate logic expression range; for example, a variable can range over the set of natural numbers, of strings, of Joe's family members, etc.
* Universal and existential quantifiers allow one to state that some condition is true for all, or for at least one, value, respectively.
* Predicates/relations. Expressions can refer to arbitrary relations; for example one can assert that two variables, ranging over the natural numbers, are equal.  Equality is a binary relation. 
* Functions


The issue of *validity* is complicated as it now has to be understood
as involving judgements of truth that are independent of any
particular interpretation.

MORE TO COME HERE.
