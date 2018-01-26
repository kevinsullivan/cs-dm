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

Pure Functional Programming as Runnable Mathematics
---------------------------------------------------

There's no free lunch: One can have the expressiveness of mathematical
logic, very useful for specification, or one can have the ability to
run code efficiently along with indispensable ability to interact with
an external environment provided by imperative code, but one can not
have both at once.

That said, there's an incredibly important point in the space between
these extremes: in *functional* as opposed to imperative *programming*
languages. Functional programming languages are based not on commands
that update memories, but simply on the definition of functions and on
their application to data values. (And by the way, functions are also
data values in such languages, so functions can be applied to functions
and functions can return other functions as results!)

Unlike mathematical logic, definitions written in functional languages
can be run, often with reasonable efficiency (though usually not with
the same efficiency as, say, C++ code). At the same time, definitions
of functions in functional languages often closely mirror their purely
mathematical definitions.

Consider, for example, the mathematical definition of the factorial
function and the implementation of this function in the functional
sub-language of Dafny. Mathematically speaking, the factorial function
is defined recursively. For any natural (non-negative whole) number,
*n, factorial(n)* is defined by two cases: if *n = 0* (we will call
this the *base case*) then *factorial(n)* is 1; otherwise, *(n > 0)*,
*factorial(n)* is *n \* factorial(n-1)*. We call this the *recursive*
case.

This kind of mathematical definition is said to be recursive, in that
the definition of *factorial* uses the factorial concept that we are
in the middle of defining! The reason that the definition makes sense,
and is not just an endless self loop, is that it is *well-founded*.
What this means is that for any *n* (a natural number), no matter how
large, the looping eventually ends. For example, *factorial(3)* is
defined to be *3 \* factorial(2).* This is *3 \* (2 \* factorial(1)).
This in turn is *3 \* 2 \* 1 \* factorial(0).* Because *factorial(0)*
is a base case, defined to be just $1$ without any further recursion,
the recursion terminates, and the end result is $3 \* 2 \* 1 \* 1*,
which finally evalutes to *6*. o matter how large *n* is, eventually
(in a finite number of steps), the recursion will bottom out at the
base case, and a result will be produced.

A functional program to compute the factorial function mirrors the
abstract mathematical definition. The program, like the definition, is
recursive in the sense that it *calls* (is defined in terms of)
itself. Here's the code in Dafny's functional programming sublanguage::

  function method fact(n: int): int 
    requires n >= 0 // for recursion to be well founded
  { 
    if (n==0) 
    then 1 
    else n * fact(n-1) 
  }

The program takes a value, $n$, of type int (any integer). Then the
requires *predicate* (a piece of logical specification) restricts the
value of $n$ to be non-negative. Finally you have the recursive rules
for computing the value of the function. If $n$ is zero the result is
one otherwise it's $n$ times the function itself applied to $n-1*.

So here you have something very interesting. First, the code is just
like the mathematics. Functional programming languages are not nearly
as expressive as predicate logic (as we'll see when we really get to
logic and proofs), but they are much closer to mathematics, in many
cases, than imperative code. Programs in pure functional languages are
more expressive and easier (for humans and machines) to reason about
than programs written in imperative languages.

Second, we now see the integration of logic and code, The $requires$
predicate is a logical proposition *about* the value of the parameter,
*n*, expressed not as a comment but as a formal and machine-checkable
part of the program.

Althird, though you can't see it here in this document, Dafny checks
to ensure that no code ever calls this function with a value of *n*
that is less than zero, *and* it proves to itself that the recursion
is well founded.  That is a lot more than you could ever expect to get
programming in an imperative language like Python.

Pure functional programming languages thus provide a way to program
functions almost as if in pure mathematics. At the same time, such
programs can be run reasonably efficiently and analyzed by human and
machanized checkers.

So what's the downside? Why not always program in such languages?  One
reason is efficiency. It's a challenge to get programs in such
languages to execute efficiency precisely because there is no notion
of a mutable memory. There's thus not way (conceptually) to update a
part of a large data structure; rather one must write a function that
takes a given data structure and that computes and builds a whole new
one, even if it differs from a given data structure only a little.

A second, even more fundamental limitation, is that there is simply no
concept of interacting with an external environment in the realm of
pure functions. You've got data values and functions that transform
given data values into new data values. And that's it. You simply
cannot do I/O in a pure functional language! There are functional
languages that are meant for practical programming (such as Haskell),
but the capabilities to do I/O are bolted on---in very clever, clean
ways, but the fact remains that I/O is just not a functional concept.

Fitting it All Together
-----------------------

So as we go forward, here's what we'll see. Ultimately, for purposes
of efficiency and interactivity (I/O), we will write imperative code
to implement software systems. That said, we can often use functional
code to implement subroutines that perform computations that do not
require mutable storage or I/O. We will *also* use pure functional
programs as parts of *specifications*. 

For example, we might specify that an *imperative* implementation of
the factorial function must take any natural number *n* as an argument
and return the value of *factorial(n)* *as defined by our functional
program for the factorial function*. The logical specification of the
imperative program will be an *implication* stating that if a proper
argument is presented, a correct result *as defined by a functional
program* will be produced.

We can thus use pure functional programs both for computation *when
appropriate*, yielding certain benefits in terms of understandability
and safety, and as elements in logical specifications of imperative
code. In Dafny, a pure functional program that is intended only for
use in specifications is declared as a $function$. A pure functional
program intended to be called from imperative code is declared as a
$function method.$ Imperative programs are simply declared as methods.

Here's a complete example: an imperative program for computing the
factorial function with a specification that first requires $n>0$
and that then requires that the result be $fact(n)$ as defined by
our functional program::

  method factorial(n: int) returns (f: int) 
    requires n>= 0
    ensures f == fact(n)
  {
    if (n==0) 
    { 
        f:= 1; 
        return;
    }
    var t := n;
    var a := 1;
    while (t !=  0)
    {
        a := a * t;
        t := t - 1;
    }
    f := a;
  }

Unfortunately Dafny reports that it cannot guarantee---formally prove
to itself---that the *postcondition* (that the result be right) will
necessarily hold. Generating proofs is hard, not only for people but
also for machines. In general it's impossibly hard, so the best that a
machine can do in practice is to try its best. If Dafny fails, as it
does in this case, what comes next is that the programmers has to give
it some help. This is done by adding some additional logic to the code
to help Dafny see its way to proving that the code satisfies the spec.

We'll see some of what's involved as we go forward in this class. We
will also eventually dive in to understand what proofs even are, and
why in general they are hard to construct. Lucky for mathematicians!
If this weren't true, they'd all be out of jobs.
