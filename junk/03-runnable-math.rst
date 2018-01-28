Pure Functional Programming as Runnable Mathematics
===================================================

What we'd really like would be a language that gives us everything:
the expressiveness and the *safety* of mathematical logic (there's no
concept of a memory in logic, and thus no possibility for unexpected
interactions through or aliasing of memory), with the efficiency and
interactivity of imperative code. Sadly, there is no such language.

Fortunately, there is an important point in the space between these
extremes: in what we call *pure functional,* as opposed to imperative,
*programming* languages. Pure functional languages are based not on
commands that update memories and perform I/O, but on the definition
of functions and their application to data values. The expressiveness
of such languages is high, in that code often directly refects the
mathematical definitions of functions. And because there is no notion
of an updateable (mutable) memory, aliasing and interactions between
far-flung parts of programs through *global variables* simply cannot
happen. Furthermore, one cannot perform I/O in such languages. These
languages thus provide far greater safety guarantees than imperative
languages.  Finally, unlike mathematical logic, code in functional
languages can be run with reasonable efficiency, though often not with
the same efficiency as in, say, C++. 

To see how functional languages allow one to implement functions in
ways that closely mirror their mathematical definitions, consider the
factorial function and an implementation of this function in the
functional *sub-language* of Dafny. (Dafny provides sub-languages for
specification and for both functional and imperative programming.)

The factorial function is defined recursively. For any natural
(non-negative whole) number, *n, factorial(n)* is defined by two
cases: one for when *n* is zero, and one for any other value of
*n*.

.. math::

   f(x)= \begin{cases} 1, & \text{if $x<0$}.\\ 0, & \text{otherwise}.\end{cases}
 

First, if *n = 0* (called the *base case*) then *factorial(n)* is
defined to be 1. Otherwise, for any *n* where *n > 0)*, *factorial(n)*
is defined recursively as *n \* factorial(n-1)*. This is what we call
the *recursive* case. By recursive, we mean that the function is used
in its own definition.

Recursive definitions are ubiquitous in mathematics. In fact, if you
get right down to it, most every function you've ever thought about is
defined recursively. For example, the addition of two natural
(non-negative) numbers *m* and *n* is defined recursively. If *m = 0*,
the base case, then the answer is *n*. If (m>0), the recursive case,
then there is some natural number *m'*, the *predecessor* of *m*, and
in this case the result is one more than (the successor of) the sum of
*m'* and *n*. such that *m = m'+1*. Recursion is thus fundamentally a
mathematical and not (just) a computational concept.

The reason that such definitions makes sense, and are not just endless
self loops, is that they are *well-founded*.  What this means is that
for any given *n* (a natural number), no matter how large, the looping
eventually ends. For example, *fact(3)* is defined to be *3 \*
fact(2).* Expanding the definition of the recursive call to the
*fact This is *3 \* (2 \* fact(1)).  This in turn is *3
\* 2 \* 1 \* fact(0).* Because *fact(0)* is a base case,
defined to be just *1* without any further recursion, the recursion
terminates, and the end result is *3 \* 2 \* 1 \* 1*, which finally
evalutes to *6*. o matter how large *n* is, eventually (in a finite
number of steps), the recursion will bottom out at the base case, and
a result will be produced.

Our functional program to compute the factorial function mirrors the
abstract mathematical definition. The program, like the definition, is
recursive: it is defined in terms of (by calling)  itself. Here's the code
in Dafny's functional programming sub-language.

.. code-block:: dafny
		
  function fact(n: int): int 
    requires n >= 0 // for recursion to be well founded
  { 
    if (n==0) 
    then 1 
    else n * fact(n-1) 
  }

The program takes a value, *n*, of type int (any integer). Then the
requires *predicate* (a piece of logical specification) restricts the
value of *n* to be non-negative. Finally you have the recursive rules
for computing the value of the function. If *n* is zero the result is
one otherwise it's *n* times the function itself applied to *n-1*.

So here you have something very interesting. First, the code is just
like the mathematics. Functional programming languages are not nearly
as expressive as predicate logic (as we'll see when we really get to
logic and proofs), but they are much closer to mathematics, in many
cases, than imperative code. Programs in pure functional languages are
more expressive and easier (for humans and machines) to reason about
than programs written in imperative languages.

Second, we now see the integration of logic and code, The *requires*
predicate is a logical proposition *about* the value of the parameter,
*n*, expressed not as a comment but as a formal and machine-checkable
part of the program.

Third, although you can't see it here in this document, Dafny checks
to ensure that no code ever calls this function with a value of *n*
that is less than zero, *and* it proves to itself that the recursion
is well founded.  That is a lot more than you could ever expect from a
typical programming system for an imperative language like Python.

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

A second, even more fundamental limitation, is that there is no
concept of interacting with an external environment in the realm of
pure functions. You've got data values and functions that transform
given values into new values, and that's it. You simply cannot do I/O
in a pure functional language! There are functional languages that are
meant for practical programming (such as Haskell), in which you can of
course do I/O, but the capabilities to do I/O are non-functional. They
are in a sense *bolted on*. They are bolted on in clever, clean ways,
but the fact remains that I/O is just not a functional concept.

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
does in this case, what comes next is that the developer has to give
it some help. This is done by adding some additional logic to the code
to help Dafny see its way to proving that the code satisfies the spec.

We'll see some of what's involved as we go forward in this class. We
will also eventually dive in to understand what proofs even are, and
why in general they are hard to construct. Lucky for mathematicians!
If this weren't true, they'd all be out of jobs. Before we go there,
though, let's have some fun and learn how to write imperative code in
Dafny.
