/-
This is Exam2 for CS2101, Spring 2018 (Sullivan).

COLLABORATION POLICY: NO COLLABORATION ALLOWED.

This is an individual evaluation. You are not
allowed to communicate with *anyone* about this 
exam, except the instructor, by any means, until
you have completed and submitted the exam and 
anyone you're communicating with has as well. Do
not communicate about this exam with anyone not
in class until all students have completed and
submitted the exam. Cheating on this exam will
result in an Honor Committee referral. Don't do
it.

You MAY use all class materials, your own notes,
and material you find through on-line searches,
or in books, or other resources, on this exam.

Note: This exam document is written using Lean,
to take advantage of Lean's support for logical
notation. It does not test any concepts that we
have covered using Lean.

The problems add up to 100 points.
-/

/- ***********************************************
Problem #1 [30 pts]. One of the basic connectives 
in propositional logic is called *equivalence*. If
P and Q are propositions, the proposition that P is
equivalent to Q is written as P ↔ Q. It can be read
as "P if and only if Q". Mathematicians shorten it
to "P iff Q." 
    
What it means is nothing other than P → Q ∧ Q → P. 
That is, P → Q and also Q → P.

In Dafny (not Lean!), the equivalence operator (a
binary Boolean operator) is written as <==>. 

Sadly, our initial implementation of propositional
logic doesn't support this operator. You job is to
extend the implementation so that it does.

(A) Extend our syntax for propositional logic with 
a new constructor, pEquiv, taking two propositions
as arguments.

(B) Extend our semantics for propositional logic
with a rule for evaluating propositions of this
form under a given interpretation.

(C) Just as the other logical connectives have
introduction and elimination rules in the natural
deduction system of logical reasoning, so does
the equivalence connective. 

The introduction  rules states that in a context
in which P → Q is true and Q → P is true then it
is valid to deduce P ↔ Q. Your job is to validate
this inference rule using the method of truth
tables. Extend consequence_test.dfy by adding a
check of this rule and confirming based on the
output of the program that it's a valid rule.

Similarly, ↔ has two elimination rules. From a
context in which P ↔ Q is true, you can deduce
by the iff left elimination rule that P → Q is
true, and from the right elimination rule that 
Q → P is true. Represent and validate these two
rules as well by extending consequence_test.dfy
accordingly.


***********************************************
Problem #2 [70 points] Open and complete the 
work required in the file Exam2.dfy.


************************************************
Submit the files syntax.dfy, evaluation.dfy, 
consequence_test.dfy, and Exam2.dfy on Collab.
The exam is due before 9:30AM next Tuesday. Do
NOT submit it late! Late submissions, if taken
at all, will have 15 points off for being late.

-/