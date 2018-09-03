/-
*** MATHEMATICAL LOGIC ***

/- *** Overview *** -/

In this unit you will learned the following concepts, among others:

* mathematical logics as formal systems
* propositions, including their syntax and semantics
* truth judgments 
* inference rules, their meaning and notation
* axioms
* proofs as evidence that justify truth judgments
* propositions about equality
* automating propositions and proofs in Lean
* an axiom defining equality in general
* type judgments
* proof trees (derivations)
* set theory and type theory as axiomatic foundations for mathematics
-/

/- *** Formal systems *** -/

/-
Modern mathematics, and discrete mathematics in particular,
are formal (mathematical) logical systems. 

Logical systems in turn are rooted in the concepts of 
propositions, truth judgments, inference rules, and 
proofs, or derivations, as evidence supporting truth
judgments.

This is pretty abstract. Let's see what it really means.
-/

/- ** Propositions and truth judgments ** -/

/-
A proposition is a mathematically precise assertion that 
some state of affairs is true in some domain of interest.

For example, in the domain of basic arithmetic, the claim
that 0 = 0 is a proposition. So is the claim that 0 = 1.

As another example, in the domain of some family unit, a
perfectly good proposition is that "Mary is the mother of
Bob." It might or might not be true in a given family,
but it's a perfectly good proposition: a claim that a
certain state of affairs holds in that domain.

Logic, then, is about making propositions precise and
above precise rules for ascertaining when any given 
proposition can be judged to be true.

Clearly we would judge the proposition, 0 = 0, to be 
true, in the domain of arithmetic. Similarly, we would
not judge the proposition 0 = 1 to be true.

Logicians will sometimes write "0 = 0 : true" as a
way to assert that the proposition, 0 = 0, is (has
been judged to be) true. We call this a truth
judgment. More generally, if P is a proposition, 
then "P : true" denotes the judgment that P is true.

EXERCISE: Write a truth judgment (just type it
in as part of this comment) for the proposition
that "Mary is the mother of Bob."

Another example of a proposition is the claim that
zero does not equal one, which we would write like
this: ¬ (0 = 1). You could pronounce this as "it is
NOT the case that 0 = 1." We would naturally judge
this proposition to be true (albeit currently just
based on our intution, not on any specific rules).

EXERCISE: Write a truth judgment here (just type it
in as part of this comment) that expresses the 
judgement that ¬ (0 = 1) is true.

Propositions, then, are claims that certain states
of affairs hold, and logic provides us with rules
for determing when a given proposition is (can be
judged to be) true.

Propositions are basically declarative statements,
asserting that "such and such" is true. What makes
them, and logic, formal is that they have a precise 
syntax, or form, and a precise semantics, or meaning.

/- * syntax * -/

Just as with computer programs, there are strict
rules that define the forms that propositions can
take, i.e., their syntax. For example, 0 = 0 is a
syntactically well-formed proposition, but 00= is
not.

/- * semantics *-/

Moreover, propositions in a given logic also have
meanings, in that they can be judged to be true,
or not, in a given domain. For example "Mary is 
the mom of Bob" (perhaps written more formally as
mother_of(Mary,Bob) is a proposition that can be 
judged to be true in some domains (family units)
and not true in others. It's true in a domain in
which Mary really is the mother of Bob, and it is
not true otherwise. 

A proposition cannot generally be judged to be 
true or false on its own. Rather, it is judged 
in some domain: under an *interpretation* that 
explains what each symbol in the proposition is 
meant  to refer to. 

For example, we could judge "Mary is the mother 
of Bob" to be true if and only if "Mary" refers 
to some person, "Bob" refers to another person, 
and under some definition of what it means to 
be the mother of, that the person referred to 
as Mary really is the mother of that person 
referred to as Bob. 

When we talk about the semantics of a logic, we 
are talking about rules for determining when some
given proposition can be judged to be true with
respect to some particular interpretation that
"maps" the symbols in the proposition to things
in the domain of discourse.

The rules for determining whether a proposition 
in a particular logic is true in a given such a
domain and interpretation is, again, called the 
semantics of that logic.

Logics thus provide rules that define the syntax
and the semantics of propositions: their forms,
and their meanings (that is, whether they are,
i.e., can be judged to be, true or not) under 
any given interpretation.

We'll dive deeper into the syntax and semantics 
of various logics as we go along. In particular,
we will discuss a simple logic, propositional
logic, and a much more useful logic, the logic 
of everyday mathematics and computer science, 
called predicate logic.

For purposes of this unit, we'll just assume 
that one particular form of valid proposition 
in predicate logic is a proposition that the 
values of two terms are equal. For example, 
0 = 0, 1 + 1 = 2, and 1 + 1 = 3 are valid 
(syntactically well formed) propositions in 
the predicate logic of everyday mathematics
and computer science.
-/

