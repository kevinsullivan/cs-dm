Dafny can't prove everything that's provable (without help)
-----------------------------------------------------------

If we had a machine that could prove any provable statement in
mathematics, we would no longer need mathematicians. Kurt Godel, whose
20th century results in mathematical logic were as profound as those
of Einstein in physics, proved once and for all that there is no such
algorithm.

It should not be surprising to learn, then, that Dafny can't prove
every provable proposition about programs. In fact, Dafny, and all
program verifiers, are fundamentally limited in what they can prove.
Sometimes what they need is some help.


// Using nat instead of int doesn't work here
//
function method fact'(n: nat): nat
{
    if n==0 then 1 else n * fact(n-1)
}
// (n-1) violates the non-negativity of the nat 
// type when n is 0 (a valid nat value). Dafny
// often catches subtle problems of this kind,
// that might escape the notice of a mere human
// programmer.
*/


/*
Here's an imperative program for computing factorial.
*/

method factorial(n: int) returns (f: int) 
    requires n >= 0
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
        invariant a * fact(t) == fact(n)
    {
        a := a * t;
        t := t - 1;
    }
    f := a;
}

/* 
Computes the sum of all of the integers from 
zero up to given non-negative integer, n. 
*/
function method sum(n: int): int 
    requires n >= 0
{
    if (n == 0) then 0 else n + sum(n-1)
}



/*
Implements addition using recursive application
of increment-by-one. To add x and y, this function 
applies the increment (inc) function x times to y. 
The value of x is restricted to non-negative values 
so that the recursion is guaranteed to terminate.
Be sure you really understand this example.
*/
function method add(x:int, y: int): int
    requires x >= 0
{
    if (x==0) then y else inc(add(x-1, y))
}


/*
Finally, here's a Main method written in imperative
style. It applies the functions we developed above
to arguments to perform simple "smoke tests" to see
if each function produces the expected results for
at least one set of arguments. 
*/
method Main()
{
    print "The value of id_int(3) is ", id_int(3), "\n";
    print "The value of square(3) is ", square(3), "\n";
    print "The value of inc(3) is ", inc(3), "\n";
    print "The value of fact(5) is ", fact(5), "\n";
    print "The value of sum(5) is ", sum(5), "\n";
    print "The value of add(4,5) is ", add(4,5), "\n";
    var fac5 := factorial(5);
    print "The value of factorial(5) is ", fac5, "\n";
}





Bar
---

definitions, consider the factorial function and an implementation of
this function in the functional *sub-language* of Dafny. (Dafny
provides sub-languages for specification and for both functional and
imperative programming.)

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

Although you can't see it here in this document, Dafny checks to
ensure that no code ever calls this function with a value of *n* that
is less than zero, *and* it proves to itself that the recursion is
well founded.  That is a lot more than you could ever expect to get
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

A second, even more fundamental limitation, is that there is no
concept of interacting with an external environment in the realm of
pure functions. You've got data values and functions that transform
given values into new values, and that's it. You simply cannot do I/O
in a pure functional language! There are functional languages that are
meant for practical programming (such as Haskell), in which you can of
course do I/O, but the capabilities to do I/O are non-functional. They
are in a sense *bolted on*. They are bolted on in clever, clean ways,
but the fact remains that I/O is just not a functional concept.

=============

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

--------

We'll see some of what's involved as we go forward in this class. We
will also eventually dive in to understand what proofs even are, and
why in general they are hard to construct.  Before we go there,
though, let's have some fun and learn how to write imperative code in
Dafny.

==

===========


   include "functional.dfy"
   module imperative {
   import opened functional

We start by prepending the function.dfy file to this one, as the
compiler needs the definitions in both files to work. We enclose the
definitions in this file in a module called *imperative*. And we
import and open the functional module in the functional.dfy file.  To
import them makes them available in this file. Opening the module
means we don't need to use the module name as a prefix to use them.


Now we give a typical imperative program for computing the factorial
function. The program takes any natural number, *n*, and returns an
answer in *f*. The value of *f* is computed first by case analysis.
If *n* is zero, the correct result, *1*, is returned. Otherwise, in
the case where *n > 0*, we *loop* to compute the factorial of *n*.

We set a variable, *a* (for *accumulator*) to *1*. Each time through
the loop we will multiply a by a value, $i$, that decreases from n to
1 as the loop runs. The loop is guaranteed to terminate in a finite
number of steps because one can only decrement a natural number value,
*i*, a finite number of times before it reaches *0*, at which point
the loop stops.

.. code-block:: dafny

   method factorial(n: nat) returns (f: nat) 
   // For any n, return the factorial of n
   {
       if (n == 0) 
       { 
           return 1;
       }
       var i: nat := n;
       var a: nat := 1;
       while (i !=  0)
       {
           a := a * n;
           i := i - 1;
       }
       return a;
   }

We have documented the specification informally in a comment akin to
the "doc strings" one uses to document Python program specifications.
The problem with this approach is that there's no practical way to
check the code against the specification expressed in the comment.
The problem with this *code* is that actually has an error, bug. Read
it carefull to see if you can find the bug before you go on. You can
see that there's a major error jst smoke testing the program. Give it
a try.

