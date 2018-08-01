/-
To this point in the course, we've seen how to 
use what we call first-order predicate logic to 
write specifications in Dafny. Dafny then tries
to prove such propositions for us. When we write
pre- and post-conditions, the effect that we've
written a proposition asserting that, "if all of
the preconditions for a method are satisfied, 
then the method will always terminate, and the
results will satisfy the given postconditions."

We've thus been able to write specifications 
to formalize concepts such as the surjective
property of a relation, R: for every element,
y, in the co-domain of R, there exists an x
in the domain of R such that (x,y) is in R.
In Dafny notation, this is written as: forall
x, y :: y in codom() ==> exists x :: x in dom()
&& (x, y) in R. In more ordinary mathematical
notation, it'd be written as ∀ y ∈ codom(R),
∃ x in dom(R) | (x,y) ∈ R. At this point in 
this course, you should be familiar enough
with these equivalent notations that you
could take English language sentences and
translate them to (formalize them in) either
of these notations.

So you've seen first-order predicate logic.
We've also not only studied and used but 
also implemented a syntax and semantics for 
propositional logic. Our prop type had as its
values expression representing propositions 
in propositional logic. Interpretations then
gave Boolean truth values to the variables
appearing in such expressions. The semantics
were then defined as an evaluator that would
give, for an expression and interpretation, 
a truth value for the expression under that
interpretation.

With all that in hand, we were then able
to write code to evaluate any proposition
in propositional logic under *all* of its
possible interpreations, and thus to write
procedures to determine whether any given
proposition in propositional logic is valid 
(always true), satisfiable (true under some
interpretations).

With that capability finally in hand, we
were able to formalize a simple concept of
inference rules, and to use our validity
checker to confirm that they are in some
important sense valid rules for reasoning.

The final insight that led to a major turn
in our thinking was that, with such rules 
in hand, we no longer need to resort to
exhaustive checking of validity using the
method of truth tables (which doesn't scale
well at all). In place of the concept of
"semantic entailment", we thus adopt the
notion of "syntactic entailment", which 
allows us to demonstrate the truth of a
given proposition by showing that we can
chain together inference rules leading
from truths determined without premises
(such as that 0=0) through intermediate
conclusions, to the final conclusion we
want to prove.

Having seen the syntax and semantics of
propositional logic, we are now in a much
better position to discuss the syntax and
semantics of first-order predicate logic,
the logical language of Dafny and also of
everyday mathematics and most of the rest
of computer science. That, in turn, will 
line us up for a brief introduction to 
the higher-order logic of Lean and of the
broader family of constructive logic proof
assistants, such as Coq.

/-
Predicate logic.

Propositional logic is a very simple logic.
Expressions can contain variables, and in
some formulations, literal truth values. A
key point is that the values of a variable
in propositional logic range over the set, 
{true, false}, and an interpretation simply
binds each variable to one of these values.
The truth value of a large proposition is
then evaluated just as if it were a Boolean
expression.

VARIABLES RANGE OVER ARBITRARY SETS

First-order predicate logic is a much more
expressive logic. First, the variables in an
expression in predicate logic can range over
*arbitrary sets*. Consider our definition of
the surjective property of relations. The
variables, x and y, range over the domain
and codomain sets of the relation, and are
not simply true and false values. 

EXPRESSIONS CAN USE RELATIONS/PREDICATES

Second, we can use *relations* in expressions 
in predicate logic. Equality and less-than are
examples of relations. In predicate logic we
can thus write propositions like, p = q → r < t.
This says if p equal q then r is less than t.
This proposition makes use of both the equals
and the less than relation on whatever sets p
and q range over.

Such relations can be viewed as predicates,
which is where the name, "predicate logic",
comes from. For example, equality is really
a predicate on pairs, (x, y): true if and
only if x and y are considered to be equal.
Remember, a predicate is a proposition with
parameters. You give the parameters, you get
back a proposition that might or might not 
be true. E.g., if you give the arguments,
3 and 4, to the = predicate, which takes
two arguments, what you get back is the
proposition, 3 = 4, which of course has
no proof in ordinary mathematics. Indeed
there is a proof of ¬(3 = 4). 


EXPRESSIONS CAN USE FUNCTIONS TO NAME VALUES

Third, we  can use functions in predicate
logic to refer to values indirectly. We can 
use the number, 9, in a proposition, but we 
could also write sqr(3) as an indirect way to
refer to 9. Similarly in a domain in which
we're talking about family histories, we
could use a function fatherOf(c) to refer
to the father of whatever person c refers
to. 


PREDICATE LOGIC HAS ∀ and ∃ QUANTIFIERS

Finally, predicate logic supports two
quantifiers: forall (∀) and exists (∃).
These quantifiers give use high expressive
power. For example, we can say in just a
few symbols what it means for any function
to be surjective. Without quantifiers, we
would be left to enumerate all individual
cases, which is infeasible when there are 
a lot of cases, and impossible when there
is an infinity of cases.
-/


At this point, we turn to the use of a 
new tool. Lean, and similar so-called
proof assistants, are engineered to help
us with natural deduction proofs in this
style of reasoning. We can write code in
them, we can write propositions, and the
notions of programs, propositions, and
proofs are unified by the "propositions
are types, proofs are values" concept.

The shift we've made has several crucial
aspects:

- From Dafny, an automated verifier that
tries to hide proofs and their derivation,
to Lean, a proof assistant, in which you,
the programmer-logicician-mathematician
work not only with propositions (as in
Dafny) but also with proofs directly.

- From the first-order
-/