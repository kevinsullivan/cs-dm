**********************************************
Dafny Language: Types, Statements, Expressions
**********************************************

Built-In Types
==============

Dafny natively supports a range of abstract data types akin to those
found in widely used, industrial imperative programming languages and
systems, such as Python and Java. In this chapter, we introduce and
briefly illustrate the use of these types. The types we discuss are
as follow:

* bool, supporting Boolean algebra
* int, nat, and real types, supporting *exact* arithmetic (unlike
  the numerical types found in most industrial languages
* char, supporting character types
* set<T> and iset<T>, polymorphic set theory for finite and infinite sets
* seq<T> and iseq<T>, polymorphic finite and infinite sequences
* string, supporting character sequences (with addtional helpful functions)
* map<K,V> and imap<K,V>, polymorphic finite and infinite partial functions
* array<T>, polymorphic 1- and multi-dimensional arrays

Booleans
--------

The bool abstract data type (ADT) in Dafny provides a bool data type
with values, *true* and *false*, along with the Boolean operators that
are supported by most programming langauges, along with a few that are
not commonly supported.

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


Numbers
-------

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


Sets
----

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
       var hi_seq := hi_seq[0 := 'H']; // update
       var b5 := 'h' in hi_seq; // member, true, !in
       var s := [0,1,2,3,4,5];
       var s1 := s[0..2];  // subseqence
       var s2 := s[1..];   // "drop" prefix of len 1
       var s3 := s[..2];   // "take" prefix of len 2
       // there's a slice operator, too; later
    }


Strings
-------

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


Maps (Partial Functions)
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


Statements
==========

Block
-----

In Dafny, you can make one bigger command from a sequence of smaller
ones by enclosing the sequence in braces. You typically use this only
for the bodies of loops and the parts of conditionals. 

.. code-block:: dafny

    {
        print "Block: Command1\n";
        print "Block: Command2\n";
    }


Break
-----

The break command is for prematurely breaking out of loops.

.. code-block:: dafny

    var i := 5;
    while (i > 0)
    {
        if (i == 3) 
        { 
            break;
        }
        i := i - 1;
    }
    print "Break: Broke when i was ", i, "\n";


Update (Assignment)
-------------------

There are several forms of the update command. The first is the usual
assignment that you see in many languages. The second is "multiple
assignment", where you can assign several values to several variables
at once. The final version is not so familar. It *chooses* a value
that satisfies some property and assigns it to a variable.


.. code-block:: dafny


    var x := 3;         // typical assignment
    var y := 4;         // typical assignment  
    print "Update: before swap, x and y are ", x, ", ", y, "\n";
    x, y := y, x;       // one-line swap using multiple assignment
    print "Update: after swap, x and y are ", x, ", ", y, "\n";
    var s: set<int> := { 1, 2, 3 }; // typical: assign set value to s
    var c :| c in s;    // update c to a value such that c is in s
    print "Update: Dafny chose this value from the set: ", c, "\n";


Var (variable declaration)
--------------------------

A variable declaration stsatement is used to declare one or more local
variables in a method or function. The type of each local variable
must be given unless the variable is given an initial value in which
case the type will be inferred. If initial values are given, the
number of values must match the number of variables declared. Note
that the type of each variable must be given individually. This "var
x, y : int;" does not declare both x and y to be of type int. Rather
it will give an error explaining that the type of x is underspecified.

.. code-block:: dafny

    var l: seq<int> := [1, 2, 3]; // explicit type (sequence of its)
    var l'          := [1, 2, 3]; // Dafny infers type from [1, 2, 3]


If (conditional)
----------------

There are several forms of the if statement in Dafny.  The first is
"if (Boolean) block-statement." The second is "if (Boolean)
block-statement else block-statement" A block is a sequence of
commands enclosed by braces (see above).

In addition, there is a multi-way if statement similar to a case
statement in C or C++. The conditions for the cases are evaluated in
an unspecified order. The first to match results in evaluation of the
corresponding command. If no case matches the overall if command does
nothing.

.. code-block:: dafny

    if (0==0) { print "If: zero is zero\n"; }   // if (bool) {block}
    if (0==1) 
        { print "If: oops!\n"; } 
    else 
        { print "If: oh good, 0 != 1\n"; }

    var q := 1;
    if {
        case q == 0 => print "Case: q is 0\n";
        case q == 1 => print "Case: q is 1\n";
        case q == 2 => print "Case: q is 2\n";
    }


While (iteration)
-----------------
    
While statements come in two forms. The first is a typical Python-like
statement "while (Boolean) block-command". The second involves the use
of a case-like construct instead of a single Boolean expression to
control the loop. This form is typically used when a loop has to
either run up or down depending on the initial value of the index. An
example of the first form is given above, for the BREAK
statement. Here is an example of the second form. 

.. code-block:: dafny

    var r: int;
    while
        decreases if 0 <= r then r else -r;
    {
        case r < 0 => { r := r + 1; }
        case 0 < r => { r := r - 1; }
    }

Dafny insists on proving that all while loops and all recursive
functions actually terminate -- do not loop forever. Proving such
properties is (infinitely) hard in general. Dafny often makes good
guesses as to how to do it, in which case one need do nothing more. In
many other cases, however, Dafny needs some help. For this, one writes
"loop specifications." These include clauses called "decreases",
"invariant", and "modifies", which are written after the while and
before the left brace of the loop body. We discuss these separately,
but in the meantime, here are a few examples.

.. code-block:: dafny

    // a loop that counts down from 5, terminating when i==0. 
    i := 5;                 // already declared as int above
    while 0 < i             
        invariant 0 <= i    // i always >= 0 before and after loop
        decreases i         // decreasing value of i bounds the loop
    {
        i := i - 1;
    }

    // this loop counts *up* from i=0 ending with i==5
    // notice that what decreases is difference between i and n
    var n := 5;
    i := 0;
    while i < n
        invariant 0 <= i <= n
        decreases n - i
    {
        i := i + 1;
    }


Assert (assert a proposition about the state of the program)
------------------------------------------------------------

Assert statements are used to express logical proposition that are
expected to be true. Dafny will attempt to prove that the assertion is
true and give an error if not. Once it has proved the assertion it can
then use its truth to aid in following deductions. Thus if Dafny is
having a difficult time verifying a method the user may help by
inserting assertions that Dafny can prove, and whose true may aid in
the larger verification effort.  (From reference manual.) 

.. code-block:: dafny

    assert i == 5;      // true because of preceding loop
    assert !(i == 4);   // similarly true
    // assert i == 4;   // uncomment to see static assertion failure


Print (produce output on console)
----------------------------------

From reference manual: The print statement is used to print the values
of a comma-separated list of expressions to the console.  The
generated C# code uses the System.Object.ToString() method to convert
the values to printable strings. The expressions may of course include
strings that are used for captions. There is no implicit new line
added, so to get a new line you should include “\n” as part of one of
the expressions. Dafny automatically creates overrides for the
ToString() method for Dafny data types.

.. code-block:: dafny

    print "Print: The set is ", { 1, 2, 3}, "\n"; // print the set


Return
------

From the reference manual: A return statement can only be used in a
method. It terminates the execution of the method. To return a value
from a method, the value is assigned to one of the named return values
before a return statement. The return values act very much like local
variables, and can be assigned to more than once. Return statements
are used when one wants to return before reaching the end of the body
block of the method.  Return statements can be just the return keyword
(where the current value of the out parameters are used), or they can
take a list of values to return. If a list is given the number of
values given must be the same as the number of named return values.

To return a value from a method, assign to the return parameter
and then either use an explicit return statement or just let the
method complete.

.. code-block:: dafny

   method ReturnExample() returns (retval: int)
   {
       retval := 10;
       // implicit return here
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
       assert 0 == 1; // can't be reached to never gets checked!
   }


Expressions
===========

Literals Expressions
--------------------

A literal expression is a boolean literal (true or false), a null
object reference (null), an unsigned integer (e.g., 3) or real (e.g.,
3.0) literal, a character (e.g., 'a') or string literal (e.g., "abc"),
or “this” which denote the current object in the context of an
instance method or function. We have not yet seen objects or talked
about instance methods or functions.

If (Conditional) Expressions
----------------------------

If expressions first evaluate a Boolean expression and then evaluate
one of the two following expressions, the first if the Boolean
expression was true, otherwise the second one.  Notice in this example
that an IF *expression* is used on the right side of an
update/assignment statement. There is also an if *statement*. 

.. code-block:: dafny

    var x := 11;
    var h := if x != 0 then (10 / x) else 1;    // if expression
    assert h == 0;
    if (h == 0) {x := 3; } else { x := 0; }     // if statement 
    assert x == 3;

Conjunction and Disjunction Expressions
---------------------------------------

Conjunction and disjuction are associative. This means that no matter
what b1, b2, and b3 are, (b1 && b2) && b3 is equal to (b1 && (b2 &&
b3)), The same property holds for ||.

These operators are also *short circuiting*. What this means is that
their second argument is evaluated only if evaluating the first does
not by itself determine the value of the expression.

Here's an example where short circuit evaluation matters. It is what
prevents the evaluation of an undefined expressions after the &&
operator.

.. code-block:: dafny

    var a: array<int> := null;  
    var b1: bool := (a != null) && (a[0]==1);

Here short circuit evaluation protects against evaluation of a[0] when
a is null. Rather than evaluating both expressions, reducing them both
to Boolean values, and then applying a Boolean *and* function, instead
the right hand expressions is evaluated "lazily", i.e., only of the
one on the left doesn't by itself determine what the result should
be. In this case, because the left hand expression is false, the whole
expression must be false, so the right side not only doesn't have to
be evaluated; it also *won't* be evaluated.


Sequence, Set, Multiset, and Map Expressions
--------------------------------------------

Values of these types can be written using so-called *display*
expressions. Sequences are written as lists of values within square
brackets; sets, within braces; and multisets using "multiset" followed
by a list of values within braces.

.. code-block:: dafny


    var aSeq: seq<int> := [1, 2, 3];
    var aVal := aSeq[1];    // get the value at index 1
    assert aVal == 2;       // don't forget about zero base indexing

    var aSet: set<int> := { 1, 2, 3};   // sets are unordered
    assert { 1, 2, 3 } == { 3, 1, 2};   // set equality ignores order
    assert [ 1, 2, 3 ] != [ 3, 1, 2];   // sequence equality doesn't

    var mSet := multiset{1, 2, 2, 3, 3, 3};
    assert (3 in mSet) == true;         // in-membership is Boolean
    assert mSet[3] == 3;                // [] counts occurrences
    assert mSet[4] == 0;

    var sqr := map [0 := 0, 1 := 1, 2 := 4, 3 := 9, 4 := 16];
    assert |sqr| == 5;
    assert sqr[2] == 4;
 
    
Relational Expressions
----------------------

Relation expressions, such as less than, have a relational operator
that compares two or more terms and returns a Boolean result. The ==,
!=, <, >, <=, and >= operators are examples. These operators are also
"chaining". That means one can write expressions such as 0 <= x < n,
and what this means is 0 <= x && x < n.

The in and !in relational operators apply to collection types. They
compute membership or non-membership respectively.

The !! operator computes disjointness of sets and multisets. Two such
collections are said to be disjoint if they have no elements in
common. Here are a few examples of relational expressions involving
collections (all given within assert statements).

.. code-block:: dafny

    assert 3 in { 1, 2, 3 };                            // set member
    assert 4 !in { 1, 2, 3 };                           // non-member
    assert "foo" in ["foo", "bar", "bar"];              // seq member
    assert "foo" in { "foo", "bar"};                    // set member
    assert { "foo", "bar" } !! { "baz", "bif"};         // disjoint
    assert { "foo", "bar" } < { "foo", "bar", "baz" };  // subset
    assert { "foo", "bar" } == { "foo", "bar" };        // set equals


Array Allocation Expressions
----------------------------

Arrays in Dafny are *reference values*. That is, the value
of an array variable is a *reference* to an address in the
*heap* part of memory, or it is *null*. To get at the data
in an array, one *dereferences* the array variable, using
the *subscripting* operator. The array variable must not be
null in this case. It must reference a chunk of memory that
has been allocated for the array values, in the *heap* part
of memory.

To allocate memory for a new array for n elements of type T one
uses an expression like this: a: array<T> := new T[n]. The type
of *a* here is "an array of elements of type *T*," and the size
of the allocated memory chunk is big enough to hold *n* values
of this type.

Multi-dimensional arrays (matrices) are also supported. The types of
these arrays are "arrayn<T>, where "n" is the number of dimensions and
T is the type of the elements. All elements of an array or matrix must
be of the same type.

.. code-block:: dafny

    a := new int[10];       // type of a already declared above
    var m: array2<int> := new int[10, 10];
    a[0] := 1;              // indexing into 1-d array
    m[0,0] := 1;            // indexing into multi-dimensional array


Old Expressions
---------------

An old expression is used in postconditions. old(e) evaluates to the
value expression e had on entry to the current method.  Here's an
example showing the use of the old expression.  This method increments
(adds one to_ the first element of an array.  The specification part
of the method *ensures* that the method body has this effect by
explaining that the new value of a[0] must be the original (the "old")
value plus one. The *requires* (preconditions) statements are needed
to ensure that the array is not null and not zero length. The modifies
command explains that the method body is allowed to change the value
of a.

.. code-block:: dafny

    method incr(a: array<nat>) returns (r: array<nat>) 
    requires a != null;
    requires a.Length > 0;
    modifies a; 
    ensures a[0] == old(a[0]) + 1;  
    {
	a[0] := a[0] + 1;
	return a;
    }



Cardinality Expressions
-----------------------

For a collection expression c, |c| is the cardinality of c. For a set
or sequence the cardinality is the number of elements. For a multiset
the cardinality is the sum of the multiplicities of the elements. For
a map the cardinality is the cardinality of the domain of the
map. Cardinality is not defined for infinite maps.

.. code-block:: dafny

    var c1 := | [1, 2, 3] |;            // cardinality of sequence
    assert c1 == 3;
    var c2 := | { 1, 2, 3 } |;          // cardinality of a set
    assert c2 == 3;
    var c3 := | map[ 0 := 0, 1 := 1, 2 := 4, 3 := 9] |; // of a map
    assert c3 == 4;
    assert | multiset{ 1, 2, 2, 3, 3, 3, 4, 4, 4, 4 } | == 10; // multiset

    
Let Expressions
---------------

A let expression allows binding of intermediate values to identifiers
for use in an expression. The start of the let expression is signaled
by the var keyword. They look like local variable declarations except
the scope of the variable only extends to following
expression. (Adapted from RefMan.)
    
Here's an example (see the following code).

First x+x is computed and bound to sum, the result of the overall
expression on the right hand side of the update/assignment statement
is then the value of "sum * sum" given this binding. The binding does
not persist past the evaluation of the "let" expression.  The
expression is called a "let" expression because in many other
languages, you'd use a let keyword to write this: let sum = x + x in
sum * sum. Dafny just uses a slightly different syntax. 

.. code-block:: dafny

    assert x == 3;               // from code above
    var sumsquared := (var sum := x + x; sum * sum);  // let example
    assert sumsquared == 36;     // because of the let expression

