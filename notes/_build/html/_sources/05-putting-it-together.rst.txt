Integrating Formal Specification with Imperative Programming
============================================================

An important approach to solving such problems is to enable the
integration of *formal specifications* with imperative programming
code along with mechansims (based on *logical proof* technology) for
checking the consistency of code with specifications. Specifications
are given not as comments but as expressions in the language of logic
right along with the code, and checkers attempt to verify that code
satisfies its corresponding *specs*.

Dafny is a cutting-edge software language and tooset developed at
Microsoft Research---one of the top computer science research labs in
the world---that provides such a capability. We will explore Dafny and
the ideas underlying it in the first part of this course, both to give
a sense of the current state of the art in program verification and,
most importantly, to explain why it's vital for a computer scientist
today to have a substantial understanding of logic and proofs along
with the ability to *code*.

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

To integrate
------------

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
and return the value of *fact(n),* our *functional* program for the
factorial function. The logical specification of the imperative
program will be an *implication* stating that if a proper argument is
presented, a correct result *as defined by a functional program* will
be produced.

We can thus use pure functional programs both for computation *when
appropriate*, yielding certain benefits in terms of understandability
and safety, and as elements in logical specifications of imperative
code. In Dafny, a pure functional program that is intended only for
use in specifications is declared as a *function*. A pure functional
program intended to be called from imperative code is declared as a
*function method.* Imperative programs are simply declared as methods.

Here's a complete example: an imperative program for computing the
factorial function with a specification that first requires *n>0*
and that then requires that the result be *fact(n)* as defined by
our functional program.

.. code-block:: dafny

   method factorial(n: nat) returns (f: nat) 
   {
       if (n == 0) 
       { 
           return 1;
       }
       var t: nat := n;
       var a: nat := 1;
       while (t !=  0)
       {
           a := a * t;
           t := t - 1;
       }
       f := a;
   }



.. code-block:: dafny

  method factorial(n: int) returns (f: int) 
    requires n>= 0
    ensures f == fact(n)
  {
    if (n == 0) 
    { 
        return 1;
    }
    var t := n;
    var a := 1;
    while (t !=  0)
    {
        a := a * t;
        t := t - 1;
    }
    return a;
  }

Unfortunately Dafny reports that it cannot guarantee---formally prove
to itself---that the *postcondition* (that the result be right) will
necessarily hold. Generating proofs is hard, not only for people but
also for machines. In general it's impossibly hard, so the best that a
machine can do in practice is to try its best. If Dafny fails, as it
does in this case, what comes next is that the developer has to give
it some help. This is done by adding some additional logic to the code
to help Dafny see its way to proving that the code satisfies the spec.

We'll see some of what's involved as we go forward in this class. We
will also eventually dive in to understand what proofs even are, and
why in general they are hard to construct. Lucky for mathematicians!
If this weren't true, they'd all be out of jobs. Before we go there,
though, let's have some fun and learn how to write imperative code in
Dafny.


