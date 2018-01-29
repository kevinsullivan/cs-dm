Logic and Code
==============

We've discussed requirements, specifications, and implementations as
software artifacts serving distinct purposes. For good reasons, these
artifacts are generally written in different languages. In this unit,
we discuss these different kinds of languages---mathematical logic for
specifications and imperative languages for code---why they are used
for different purposes, the fundamental advantages and disadvantages
of each, and why modern software development requires fluence in and
tools for handling artifacts written in multiple such languages.

Imperative Implementations and Declarative Specifications
---------------------------------------------------------

The language of implementations is code in what we call an *imperative
programming language*. Examples of such languages include Python,
Java, C++, and Javascript. The most salient property of such a
language is that it is *procedural*. Programs in these languages
describe step-by-step *procedures*, in the form of sequences of
*commands*, for solving given problem instances. Commands in such
languages operate by (1) reading, computing with, and updating values
stored in a *mutable memory*, and (2) interacting with the world
outside of the computer by executing input and output (IO) commands.

The language of formal requirements and specifications, on the other
hand, is some kind of *mathematical logic*. Examples of logics that we
will study and use include *propositional* and *predicate* logic.  An
example of a kind of logic important in software development but that
we will not study in this class is *temporal logic.*

For purposes of software specification, the most salient property of
such a logical language is that it is *declarative*.  Expressions in
logic will state *what* properties or relationships must hold in a
given situation, particularly how results must relate to inputs,
without providing executable, step-by-step procedures describing *how*
to actually compute such relationships.

To make the difference between procedural and declarative styles of
description clear, consider the problem of computing the positive
square root of a given non-negative number, *x*. We can *specify* the
answer in a clear and precise logical style by simply stating that,
for any given non-negative number *x*, we require a value, *y*, such
that :math:`y^2 = x`. We would write this mathematically as
:math:`\forall x \mid x >= 0, sqrt(x) = y | y^2 = x`. In English, we'd
pronounce this formula as, "for any *x* where *x* is greater than or
equal to zero, the square root of *x* is a value *y* such that *y*
squared is equal to *x*."

We now have a *declarative specification* of the desired relationship
between *x* and *y*. What we don't have, however, is a step-by-step
*procedure* for computing this relation by finding a value of *y* for
any given value of *x*. You can't just run a specification written in
the language of mathematical logic.

The solution is to shift from mathematics as a specification language
to imperative code as an implementation language.  In such a language,
we then craft a step-by-step procedure that, when run, computes the
results we seek. Here's an example of a program in the imperative
language, Python, for computing positive square roots of non-negative
numbers using Newton's method.

.. code-block:: python

  def sqrt(x):
      """for x>=0, return non-negative y such that y^2 = x"""
      estimate = x/2
      while True:
          newestimate = ((estimate+(x/estimate))/2)
          if newestimate == estimate:
              break
          estimate = newestimate
      return estimate


This procedure initializes and then repeatedly updates the values
stored at two locations in memory, referred to by the two variables,
*estimate* and *newestimate*. It repeats the update process until the
process *converges* on the answer, which occurs when the values of the
two variables become equal. The answer is then returned to the caller
of this procedure.

Note that, following good programming style, we included an English
rendering of the specification as a document string in the second line
of the program.  There are however several deep problems with this
approach. First, as we've discussed, natural language is subject to
ambiguity, inconsistency, and incompleteness. Second, because the
document string is just a comment, there's no way for the compiler to
check consistency between the code and this specification. Third, in
practice, code evolves (changes over time), and in their rush to ship
code, developers often forget, or neglect, to update comments. So, in
practice, even if a given procedure is initially consistent with a
specification given as comment, inconsistencies can and often do
develop over time.


Why Not a Single Language for both Programming and Specification?
-----------------------------------------------------------------

The dichotomy between specification logic and implementation code
raises an important question? Why not just design a single language
that's good for both?

The answer is that there are fundamental tradeoffs in language design.
One of the most important is a tradeoff between *expressiveness*, on
one hand, and *efficient execution*, on the other.

What we see in our square root example is that mathematical logic is
highly *expressive*. Logic language can be used so say very clearly
*what* we want. On the other hand, it's hard using logic to say *how*
to get it. In practice, mathematical logic is clear but can't be *run*
(at least not efficiently).

On the other hand, imperative code states *how* a computation is to be
carried out, but enerally doesn't make clear *what* it's computing. You
would be hard-pressed, based on a quick look at the Python code above,
to explain *what* it does (but for the fact that we embedded the spec
into the code as a doc string).

We are driven to a situation in which we have to express what we want
and how to get it, respectively, in very different languages. This
situation creates a difficult new problem: to verify that a program
written in an imperative language satisfies a specification written in
a declarative language.  This is the problem of *verification*. Have
we built a program right (where right is defined by a specification)?

