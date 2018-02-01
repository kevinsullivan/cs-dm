Requirement, Specifications, and Implementations
================================================

Software is an increasingly critical component of major societal
systems, from rockets to power grids to healthcare, etc. Failures are
not always bugs in implementation code. The most critical problems
today are not in implementations but in requirements and
specifications.

* **Requirements:** Statements of the effects that a system is meant to have in a given domain
* **Specification:** Statements of the behavior required of a machine to produce such effects
* **Implementation:** The definition (usually in code) of how a machine produces the specified behavior

Avoiding software-caused system failures requires not only a solid
understanding of requirements, specifications, and implementations,
but also great care in both the *validation* of requirements and of
specifications, and *verification* of code against specifications.

* **Validation:** *Are we building the right system?* is the specification right; are the requirements right?
* **Verification:** *Are we building the system right?* Does the implementation behave as its specification requires?

You know that the language of implementation is code. What is the
language of specification and of requirements?

One possible answer is *natural language*. Requirements and
specifications can be written in natural languages such as English or
Mandarin. The problem is that natural language is subject to
ambiguity, incompleteness, and inconsistency. This makes it a risky
medium for communicating the precise behaviors required of complex
software artifacts.

The alternative to natural language that we will explore in this class
is the use of mathematical logic, in particular what we call propositional
logic, predicate logic, set theory, and the related field of type theory.

Propositional logic is a language of simple propositions. Propositions
are assertions that might or might not be judged to be true. For
example, *Tennys (the person) plays tennis* is actually a true
proposition (if we interpret *Tennys* to be the person who just played
in the French Open).  So is *Tennys is from Tennessee*. And because
these two propositions are true, so is the *compound* proposition (a
proposition built up from smaller propositions) that Tennys is from
Tennessee **and** Tennys plans tennis.

Sometimes we want to talk about whether different entities satisfy
give propositions. For this, we introduce propositions with parameters,
which we will call *properties*. If we take *Tennys* out of *Tennys
plays tennis* and replace his name by a variable, *P*, that can take
on the identify of any person, then we end up with a parameterized
proposition, *P plays tennis*. Substituting the name of any particular
person for *P* then gives us a proposition *about that person* that we
can judge to be true or false. A parameterized proposition thus gives
rise to a whole family of propositions, one for each possible value of
*P*.

Sometimes we write parameterized propositions so that they look like
functions, like this: *PlaysTennis(P)*. *PlaysTennis(Tennys)* is thus
the proposition, *Tennys plays Tennis* while *PlaysTennis(Kevin)* is
the proposition *Kevin plays Tennis*. For each possible person name,
*P*, there is a corresponding proposition, *PlaysTennis(P)*.

Some such propositions might be true. For instance,
*PlaysTennis(Tennys)* is true in our example. Others might be false. A
parameterized proposition thus encodes a *property* that some things
(here people) have and that others don't have (here, the property of
*being a tennis player*).

A property, also sometimes called a *predicate*, thus also serves to
identify a *subset* of elements in a given *domain of discourse*. Here
the domain of discourse is the of all people. The subset of people who
actually do *play tennis* is exactly the set of people, P, for whom
*PlaysTennis(P)* is true. 

We note briefly, here, that, like functions, propositions can have
multiple parameters. For example, we can generalize from *Tennys plays
Tennis **and** Tennys is from Tennessee* to *P plays tennis and P is
from L,* where P ranges over people and L ranges over locations. We
call a proposition with two or more parameters a *relation*. A
relation picks out *combinations* of elements for which corresponding
properties are true. So, for example, the *pair* (Tennys, Tennessee)
is in the relation (set of *P-L* pairs) picked out by this
parameterized proposition. On the other hand, the pair, (Kevin,
Tennessee), is not, because Kevin is actually from New Hampshire, so
the proposition *Kevin plays tennis **and** Kevin is from Tennessee*
is not true. More on relations later!
