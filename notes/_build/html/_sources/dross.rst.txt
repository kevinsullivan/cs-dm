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



====

Indeed, natural science is based to a considerable extent on inductive
reasoning. Observations in the form of tests of hypotheses are taken
as evidence in support of hypotheses about how the world works. When
there is a sufficient body of evidence, a hypothesis is elevated to a
theory.  Statistical techniques are often used to quanitfy remaining
doubt.  Theories are always subject to falsification in principle,
though in practice the evidence for some theories is so strong that
for all intents and purposes, some questions are all but settled, and
acting on alternative hypotheses would be irrational.

 ====

 A Syntax for Boolean Expressions
--------------------------------

How can we precisely and concisely specify the entire (infinite) set
of well formed Boolean expressions? In this section, we will find an
answer in the concept of *inductive definitions*, which are closely
related to recursive functions.

We'll define what it means to be a Boolean expression using several
cases, some of which will explain how to form larger such expressions
from smaller ones, ad infinitum. So here we go.

Case #1: Literal Expressions. For each Boolean value, *b* (*0 or 1*)
we have a corresponding Boolean expression, *Lit(b)*. So far, then, we
have just two Boolean expressions: *Lit(true)* and *Lit(false)*. We
can think of *Lit* as a kind of function that takes a Boolean value
and that constructs a Boolean expression from it. 

Case #2: Boolean Variables. We will assume that we have some set of
*Boolean variables*. For simplicity, let's assume that this set is
:math:`\{ P, Q, R \}`. For each variable, $V$, we have a corresponding
Boolean expression, $BVar(V)$. Now we have three more expressions,
*BVar(P)$, *BVar(Q)* and *BVar(R)*.



First, we will
define two *literal* expressions, one for each of the two Boolean
values. We will call them *BLit(0)* and *BLit(1)*.
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
For each kind of expression we will also need a way to *evaluate* it:
to say what Boolean value it evaluates to. For this, we will define a
function that (for now) takes a Boolean *expression* as an argument
and that returns a Boolean *value* as a result. We will call this
evaluation function for Boolean expressions *beval*.

Now we need to explain how this function behaves for each of the kinds
of Boolean expressions we have defined do far. This is an easy one. We
will define *beval(BLit(0))* to evaluate to *0*, and *beval(BLit(1))*
to evaluate to *1*.


Boolean logic is named after its inventor, George Boole,
the British philosopher, mathematician, and logician.

Dafny supports a range of abstract data types akin to those found in
widely used, industrial imperative programming languages and systems,
such as Python and Java. In this chapter, we introduce and briefly
illustrate the use of these types. The types we discuss are as follow:

* bool, supporting Boolean algebra
* int, nat, and real types, supporting *exact* arithmetic (unlike
  the numerical types found in most industrial languages
* char, supporting character types
* set<T> and iset<T>, polymorphic set theory for finite and infinite sets
* seq<T> and iseq<T>, polymorphic finite and infinite sequences
* string, supporting character sequences (with addtional helpful functions)
* map<K,V> and imap<K,V>, polymorphic finite and infinite partial functions
* array<T>, polymorphic 1- and multi-dimensional arrays

Boolean Algebra
---------------


====

The bool abstract data type (ADT) in Dafny provides a bool data type
with values, *true* and *false*, along with the Boolean operators that
are supported by most programming langauges, along with a few that are
not commonly supported by industrial programming languages and
systems.

Here's a method that computes nothing useful and returns no values,
but that illustrates the range of Boolean operators in Dafny. We also
use the examples in this chapter to discuss a few other aspects of the
Dafny language.

.. code-block:: dafny

   method BoolOps(a: bool) returns (r: bool)  // bool -> bool
   {
       var t: bool := true;    // explicit type declaration
       var f := false;         // type inferred automatically
       var not := !t;          // negation
       var conj := t && f;     // conjunction, short-circuit evaluation
       var disj := t || f;     // disjunction, short-circuit (sc) evaluation
       var impl := t ==> f;    // implication, right associative, sc from left
       var foll := t <== f;    // follows, left associative, sc from right
       var equv := t <==> t;   // iff, bi-implication
       return true;            // returning a Boolean value
    }


Arithmetic
----------

Methods aren't required to return results. Such methods do their jobs
by having side effects, e.g., doing output or writing data into global
variables (usually a bad idea).  Here's a method that doesn't return a
value. It illustrates numerical types, syntax, and operations.

.. code-block:: dafny

   method NumOps()
   {
       var r1: real := 1000000.0;
       var i1: int := 1000000;
       var i2: int := 1_000_000;   // underscores for readiability
       var i3 := 1_000;            // Dafny can often infer types
       var b1 := (10 < 20) && (20 <= 30); // a boolean expression
       var b2 := 10 < 20 <= 30;    // equivalent, with "chaining"
       var i4: int := (5.5).Floor; // 5
       var i5 := (-2.5).Floor;     // -3
       var i6 := -2.5.Floor;        // -2 = -(2.5.Floor); binding!
   }


Characters
----------

Characters (char) are handled sort of as they are in C, etc.

.. code-block:: dafny

   method CharFun()
   {
       var c1: char := 'a';
       var c2 := 'b';
       // var i1 := c2 - c1;
       var i1 := (c2 as int) - (c1 as int);    // type conversion
       var b1 := c1 < c2;  // ordering operators defined for char
       var c3 := '\n';     // c-style escape for non-printing chars
       var c4 := '\u265B'; // unicode, hex, "chess king" character
   }

To return a value from a method, assign to the return parameter
Note: functions have colon then return type, whereas methods 
use the "returns" keyword with a return parameter list

.. code-block:: dafny

   method ReturnExample() returns (retval: int)
   {
       retval := 10;
   }

Methods can return multiple values.

.. code-block:: dafny

   method ReturnExample2() returns (x: int, y:int)
   {
       x := 10; 
       y := 20;
}

The return keyword can be used to return immediatey

.. code-block:: dafny

   method ReturnExample3() returns (x: int)
   {
       x := 5;     // don't "var" decare return variable
       return;     // return immediately
       x := 6;     // never gets executed
   }

Set Theory
-----------

Polymorphic finite and infinite set types:
set<T> and iset<T>. T must support equality.
Values of these types are immutable.

.. code-block:: dafny

   method SetPlay()
   {
       var empty: set<int> := {};
       var primes := {2, 3, 5, 7, 11};
       var squares := {1, 4, 9, 16, 25};
       var b1 := empty < primes;    // strict subset
       var b2 := primes <= primes;   // subset
       var b3: bool := primes !! squares; // disjoint
       var union := primes + squares;
       var intersection := primes * squares;
       var difference := primes - {3, 5};
       var b4 := primes == squares;    // false
       var i1 := | primes |;   // cardinality (5)
       var b5 := 4 in primes;  // membership (false)
       var b6 := 4 !in primes; // non-membership
   }


Sequences
---------

Polymorphic sequences (often called "lists"): seq<T>. These can be
understood as functions from indices to values. Some of the operations
require that T support equality. Values of this type are immutable.

.. code-block:: dafny

   method SequencePlay()
   {
       var empty_seq: seq<char> := [];
       var hi_seq: seq<char> := ['h', 'i'];
       var b1 := hi_seq == empty_seq; // equality; !=
       var hchar := hi_seq[0];        // indexing 
       var b2 := ['h'] < hi_seq;   // proper prefix
       var b3 := hi_seq < hi_seq;  // this is false
       var b4 := hi_seq <= hi_seq; // prefix, true
       var sum := hi_seq + hi_seq; // concatenation
       var len := | hi_seq |;
       var Hi_seq := hi_seq[0 := 'H']; // update
       var b5 := 'h' in hi_seq; // member, true, !in
       var s := [0,1,2,3,4,5];
       var s1 := s[0..2];  // subseqence
       var s2 := s[1..];   // "drop" prefix of len 1
       var s3 := s[..2];   // "take" prefix of len 2
       // there's a slice operator, too; later
    }


Character Strings
-----------------

Dafny has strings. Strings are literally just sequences of characters
(of type seq<char>), so you can use all the sequence operations on
strings.  Dafny provides additional helpful syntax for strings.


.. code-block:: dafny

   method StringPlay() 
    {
        var s1: string := "Hello CS2102!";
        var s2 := "Hello CS2102!\n";   // return
        var s3 := "\"Hello CS2102!\""; // quotes
    }


Partial Functions (Maps)
------------------------

Dafny also supports polymorphic maps, both finite (map<K,V>) and
infinite (imap<K,V>).  The key type, K, must support equality (==).
In mathematical terms, a map really represents a binary relation,
i.e., a set of <K,V> pairs, which is to say a subset of the product
set, K * V, where we view the types K and V as defining sets of
values.

.. code-block:: dafny

   method MapPlay()
   {
       // A map literal is keyword map + a list of maplets.
       // A maplet is just a single <K,V> pair (or "tuple").
       // Here's an empty map from strings to ints
       var emptyMap: map<string,int> := map[];
   
       // Here's non empty map from strings to ints
       // A maplet is "k := v," k and v being of types K and V
       var aMap: map<string,int>  := map["Hi" := 1, "There" := 2];
   
       // Map domain (key) membership
       var isIn: bool := "There" in aMap; // true
       var isntIn := "Their" !in aMap;    // true
   
       // Finite map cardinality (number of maplets in a map)
       var card := |aMap|;
   
       //Map lookup
       var image1 := aMap["There"];
       // var image2 := aMap["Their"]; // error! some kind of magic
       var image2: int;
       if ("Their" in aMap) { image2 := aMap["Their"]; }
   
       // map update, maplet override and maplet addition
       aMap := aMap["There" := 3];
       aMap := aMap["Their" := 10];  
   }


Arrays
------

Dafny supports arrays. Here's we'll see simple 1-d arrays.

.. code-block:: dafny

   method ArrayPlay() 
   {
       var a := new int[10]; // in general: a: array<T> := new T[n];
       var a' := new int[10];   // type inference naturally works here
       var i1 := a.Length;      // Immutable "Length" member holds length of array
       a[3] := 3;           // array update
       var i2 := a[3];          // array access
       var seq1 := a[3..8];    // take first 8, drop first 3, return as sequence
       var b := 3 in seq1;     // true! (see sequence operations)
       var seq2 := a[..8];     // take first 8, return rest as sequence
       var seq3 := a[3..];     // drop first 3, return rest as sequence
       var seq4 := a[..];      // return entire array as a sequence
   }

Arrays, objects (class instances), and traits (to be discussed) are of
"reference" types, which is to say, values of these types are stored
on the heap. Values of other types, including sets and sequences, are
of "value types," which is to say values of these types are stored on
the stack; and they're thus always treated as "local" variables. They
are passed by value, not reference, when passed as arguments to
functions and methods. Value types include the basic scalar types
(bool, char, nat, int, real), built-in collection types (set,
multiset, seq, string, map, imap), tuple, inductive, and co-inductive
types (to be discussed).  Reference type values are allocated
dynamically on the heap, are passed by reference, and therefore can be
"side effected" (mofified) by methods to which they are passed.
