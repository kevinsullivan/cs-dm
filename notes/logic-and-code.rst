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
description clear, consider the problem of computing the square root
of a given non-negative number, *x*. We can *specify* the answer in a
clear and precise mathematical logical style by simply stating that,
for any given non-negative number *x*, we require a value, *y*, such
that *y^2 = x*. We can write this mathematically as *for all x >= 0,
sqrt(x) = y | y^2 = x*. In English, we'd pronounce this formula as, "
for any non-negative value, *x*, a square root of *x* is a value *y*
such that *y* squared is equal to *x*." We now have a *declarative
specification* of the desired relationship between *x* and *y* that a
program for computing square roots must compute. What we don't have,
however, is a step-by-step *procedure* for computing this relation by
finding a satisfactory value of *y* given any *x*). You can't just run
a specification written in the language of mathematical logic.

The solution is to shift from a specification to an implementation
language: from mathematical logic as a specification language to an
imperative programming language in which we can write code that runs.
And in this implementation language, we must then craft a step-by-step
procedures that when evaluted actually computes the results we seek.

Here's an example of a program in the imperative language, Python, for
computing positive square roots of non-negative numbers using Newton's
method::

    def sqrt(x):
        """for x>=0, return non-negative y such that y^2 = x"""
        estimate = x/2
        while True:
            newestimate = ((estimate+(x/estimate))/2)
            if newestimate == estimate:
                break
            estimate = newestimate
        return estimate

This procedure updates the values stored at two locations in memory
referred to by the variables, *estimate* and *newestimate*. It repeats
the update process until the process *converges* on the answer, which
occurs when the values of the two variables become equal. The result
is then returned to the caller of this procedure.

Note that, following good programming style, we included the
specification of the procedure as a document string in the second line
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


Integrating Formal Specification with Imperative Programming
------------------------------------------------------------

A vitally important approach to solving such problems is to enable the
integration of *formal specifications* with imperative programming
code along with mechansims (based on *logical proof* technology) for
checking the consistency of code with specifications. Specifications
are given not as comments but as expressions in the language of logic
right along with the code, and checkers attempt to verify that code
satisfies its corresponding *specs*.

Dafny is a cutting-ede software language and tooset developed at
Microsoft Research---one of the top computer science research labs in
the world---that provides such a capability. We will explore Dafny and
the ideas underlying it in the first part of this course, both to give
a sense of the current state of the art in program verification and,
most importantly, to explain why it's vital for a computer scientist
today to have a substantial understanding of logic and proofs along
with the ability to *code*.

Why Not a Single Language for both Programming and Specification?
-----------------------------------------------------------------

The dichotomy between specification logic and implementation code
raises an important question? Why not just design a single language
that's good for both?

The answer is that there are fundamental tradeoffs in language design.
The most important is a tradeoff between *expressiveness*, on one
hand, and *efficient execution*, on the other.

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

We are thus driven to a situation in which we have to express what we
want and how to get it respectively, in very different languages. This
situation creates a difficult new problem: to verify that a program in
one language satisfies a specification in a different language.  This
is the problem of *verification*. Have we built a given program right
(where right is defined by a specification)?

Tools such as TLA+, Dafny, and others of this variety give us a way
both to express formal specifications and imperative code in a unified
way (albeit in different sub-languages), and to have some automated
checking done in an *attempt* to verify that code satisfies its spec.

We say *attempt* here, because in general verifying the consistency of
code and a specification is a literally unsolvable problem. In cases
that arise in practice, much can often be done. It's not always easy,
but if one requires ultra-high assurance of the consistency of code
and specification, then there is no choice but to employ the kinds of
*formal methods* introduced here.

To understand how to use such state-of-the-art software development
tools and methods, one must understand not only the language of code,
but also the languages of mathematical logic, including set and type
theory. One must also understand precisely what it means to *prove*
that a program satisfies its specification; for generating proofs is
exactly what tools like Dafny do *under the hood*.

A well educated computer scientist and a professionally trained
software developer must understand logic and proofs as well as coding,
and how they work together to help build *trustworthy* systems. Herein
lies the deep relevance of logic and proofs, which might otherwise
seem like little more than abstract nonsense and a distraction from
the task of learning how to program. 
