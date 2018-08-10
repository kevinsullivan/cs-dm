/-
In this unit, we implement our own version of the Boolean algebra
already built into Lean. We will define our own version of Lean's
bool type, and our own versions of its and, or, and not operators.
-/

/-
In doing this, we will encounter several important concepts in
Lean, which are also shared by many other languages. They include
the following:

- namespaces
- inductive type definitions 
- sets, product sets, tuples, binary relations, and functions
- type judgments, type declarations, and type inference
- function types and function values
- functional programing: case analysis via pattern matching
-/

-- NAMESPACES

/-
If we just jump in and try to define our own version of the type
called bool, our version would conflict with the one that is already 
provided (as we've just seen) by Lean. To see the problem, uncomment
the following code and see the resulting error, stating that the 
current "environment" (associating meanings with identifiers)
already has an assigned meaning for the identifier, bool.
-/

/-
inductive bool : Type 
| tt : bool
| ff : bool
-/


/-
To avoid such conflicts, we will give our own definition to the
identifier, "bool", in a separate "namespace." We'll call it cs2102.
-/

namespace uvacs.csdm.xbool

/-
What this means is that every name, such as bool, that we define in this
namespace is actually prefixed with cs2102. So the name, bool, is really
now cs2102.bool. If you go to the end of this file, you'll see "end cs2102",
defining the closing boundary of this namespace. Go look now. Delete that
line and see what error you get. Put the line back in then come back to
this point in this file and continue forwards.
-/

/-
With that ancillary detail out of the way we can now turn to the
main content of this chapter, giving our own implementation of 
Boolean algebra, comprising (1) a definition of the set of values,
and (2) a definition of a set of operations closed on this set. We
start by defining the so-called "carrier set" of values by defining
a type.
-/


/-
**** INDUCTIVE DEFINITIONS OF TYPES: CASE STUDY OF bool ****
-/

/-
In Lean and in many other functional languages, we define types
"inductively" by specifying a set of "constructors." A constructor
has a name and optional parameter values, each with its own type. 
A constructor with no parameters is taken to be a value of a given
type. We will see constructors with parameters later. The set of 
values of a give type is the set of values that can be built by 
using the available constructors.

What we want to do here is define the carrier set for our own
implementation of Boolean algebra. The set has two values, usually
called true and false. Following Lean's lead, we will call them
tt and ff. We can use a type with two parameterless constructors,
one called tt and one called ff to this end.

Here then is the inductive definition of our version of the bool type. 
It starts with the keyword, inductive, followed by the name of the type, 
bool, and a judgment that indicates that bool is a type. Following this
judgement is a list of constructors, each starting with a vertial bar 
followed by the name of the constructor and its type. 
-/

inductive bool : Type
| ff : bool
| tt : bool

/-
This definition thus says that ff and tt are values of type bool. 
Because the set of values of a type includes all and only the values
that can be built by the available constructors, tt and ff are both
values of this type and they are the only values of this type. The 
set of values defined in this way is thus the set, { tt, ff }. 
-/

/-
We've thus got half of our algebra defined: the carrier set of values!
To complete our implementation of Boolean algebra, we need to define
a set of operations -- already familiar to you from CS1 -- closed on
this set. These operations include such things as the and, or, and not
operators on Boolean values. Take a minute to recall exactly how these
operators work.
-/

/-
Before we proceed to define functional programs that implement
these operations, we take a short diversion to deep our understanding
of namespaces. We now have two different definitions of bool, and of
the constructors tt and ff: one that we've given, and one that comes
native to Lean. So let's dig in. 
-/

-- MORE ON NAMESPACES

/-
A type definition establishes a new definition for the name of the
type, here bool. It also implicitly defines its own namespace, nested 
within the prevailing namespace, within which the constructor names
are defined. In the current environment, the name bool is thus really 
cs2102.bool, and the names of our constructors, tt and ff, are really
cs2102.bool.tt and cs2102.bool.ff. Like many programming languages,
Lean provides defaults that often let us leave off the "qualifiers,"
with Lean figuring out what we mean by context. 
-/

-- EXPRESSIONS, TYPES, AND LITERAL EXPRESSIONS, IN PARTICULAR

/-
The #check command in Lean can be used to determine the type of an
identifier, value, or expression. An expressions in the form of a
simple name name that has been defined to have some value is called
a "literal" expression.

Hover your mouse over the #check command to check the type of the
literal expression, bool. Lean will tell you that the type of bool 
is Type. Yep, a type, such as bool, is itself a value, and so has 
a type! And its type -- the type of any such type -- is Type! 

Moreover, as the following command shows, the name, "bool", refers, 
in the current contexts, to our local definition of bool, which we 
can write out in full as cs2102.bool. The name does not refer, in
the current environment, to the built-in definition of bool in the 
so-called _root_ namespace.
-/

#check bool
#check _root_.bool

/-
Hover your mouse over "bool." Lean will confirm what we just said.
Similarly, hover over _root_.bool. Notice that it's not the version
of bool defined in our cs2102 namespace. Rather, it's the version 
defined in the _root_ namespace, which is established when Lean is
started.
-/

/-
Similarly, you can confirm that the type of the literal expression,
and thus the type of the value, bool.tt, is bool (think about that!). 
You can also re-confirm here that the definition of bool in use in 
this context is cs2102.bool.
-/
#check bool.tt

-- NESTED NAMESPACES ESTABLISHED BY INDUCTIVE TYPE DEFINITIONS

/-
The next important concept related to namespaces is that each
inductive type definition introduces its own namespace, with the
same name as the type name, within which its constructor names
are defined. Importantly, such namespaces are not "open" by
default. What that means is that you can't refer to constructors
by name without the type name as a qualifier. Here's a silly type
definition to make the point.
-/

inductive silly_type : Type 
| silly_a : silly_type
| silly_b : silly_type

/-
The name, silly_type, is now defined in the current environment.
-/

#check silly_type

/-
But the name silly_a isn't; you have to use silly_type.silly_a
to refer to it. Uncomment the first line that follows to confirm
that you get an error (hover over the red line to see the error
details), then confirm that the second #check is good.
-/

-- #check silly_a
#check silly_type.silly_a



-- OPENING NAMESPACES

/-
It's inconvenient to always have to type namespace names to refer
to definitions inside of namespaces. To address this issue, Lean,
and many other languages, allow you to "open" a namespace, after
which you can refer directly to names defined within it.
-/

open silly_type
#check silly_a -- yeah!

/-
In the first part of this class, we're going to define our own
versions of some of the fundamental types already built into Lean
(via libraries that it imports automatically). Those types are
defined in the global, or "root", namespace of Lean. To avoid
having our definitions conflict with those in the root namespace
We enclose all of our own definitions within a namespace called 
"csdm", short for "computer science discrete math." 
-/


/-
One must be quite careful when defining names that are already 
defined in other namespaces that you might be using. To give a
sense of the issue, stop to address the following exercise.
-/

/-
EXERCISE: In the current environment (the association between
names and their meanings) what is the meaning of the identifier,
bool? Is it the version of bool from the root namespace or is 
it our bool from the csdm namespace? 

EXERCISE: What about tt? Does its definition in the current
environment come from from the bool type in the root namespace 
or from our bool type's namespace?
-/

/-
Answering these question requires some non-trivial reasoning. 
Luckily, you can use Lean #check commands to test your answers.
-/

/-
First, in the current environment (at this point in the code),
the identifier, bool, refers to our version of bool. We defined
the name in the current namespace, so our definition prevails.
If you want to refer to the version of bool in the root namespace,
you have to use _root_.bool
-/

#check bool
#check _root_.bool

/-
The situation with tt is more complex. The key to understanding
the answer is to remember that the namespaces of types are closed
by default. So even though we've defined our own version of bool
in the current environment, its namespace, within which the names 
of its constructors are defined, is still closed. Therefore we
can't just use tt and ff to refer to those constructors.

On the other hand, the names, tt and ff, from the by-default 
opened namespace of the bool type in the root namespace to be
visible into the current namespace. So at this point, tt refers 
to _root_.bool.tt. 

If we want to refer to our version of tt, a qualified name has 
to be used. It can be bool.tt or to be completely clear, you 
can use csdm.bool.tt. They mean the same thing. Hover over the
identifiers in the following #check commands to confirm what we 
just said.
-/

#check tt
#check bool.tt
#check csdm.bool.tt

/-
To summarize, in this environment, bool refers to csdm.bool, 
bool.tt thus refers to csdm.bool.tt, which we call the "fully 
qualified" name of this constructor. But tt refers to the tt 
constructor defined by the built-in version of the bool type.
-/

-- AMBIGUOUS DEFINITIONS

/-
Now the astute reader might suggest that all we have to do 
is to open the csdm.bool namespace. That's actually a good
idea, but there's a complication: we end up with two definitions
of the same identifier in the same current environment! The
first is the definition visible in the _root_ namespace, and
the second is the one from our own bool type definition. 
Here's the command to open csdm.bool.
-/

open csdm.bool 

/-
The problem is that two different definitions of tt are now
visible in the current environment. That is, the definition of
the identifier is ambiguous. 

Uncomment the following line by deleting the two underscores
at the beginning of the and hover over the red line to see the 
error  message. It says that the definition of tt is ambiguous
in the current environment. 
-/

--#check tt --ambiguous!

/-
To refer to our own definition of tt, you thus once again have 
to use a qualified name. Either of the following forms will do.
-/

#check bool.tt -- this now refers to *our* version of tt
#check csdm.bool.tt -- so does this!

/-
Moreover, you can no longer refer to the definition of tt from
the root environment just by writing tt: tt is ambiguous now.
To refer either to the bool type or to one of its constructors 
from the root namespace, you now have to do so using the special 
namespace designator. At a technical level, _root_ is not itself
a namespace, but it tells Lean that that's the namespace in which
to look for a definition of the following name.
-/

#check _root_.bool -- the _root_ tells lean to use the built-in version
#check _root_.bool.tt

/-
For the reader who wants the full picture, there's one final,
and admittedly confusing point. Even though in the current environment,
bool refers to our definition of bool, in the context of an open command,
that is not so. Rather, "bool" refers to the built-in version. This is
arguably a design flaw in Lean. The following command thus opens the 
namespace of the bool type in the root environment; but it's already 
open so the command has no further effect!
-/

open bool

/-
The takeaway is that when you use an open command, you should use a 
qualified name, as we did above when we opened cs2012.bool (not just
bool). 
-/

/-
The interested reader may (but is not expected to) refer to the
Lean reference manual for additional information on namespaces.
https://leanprover.github.io/reference/other_commands.html#namespaces
-/

/- 
 **** MATHEMATICAL FUNCTIONS AND PURE FUNCTIONAL PROGRAMS ****
-/

/-
We now get back to the main point of this chapter to complete
our implementation of the algebra known as Boolean algebra. We
have already defined the carrier set, bool = { tt, ff }, as the
type, bool. Now we have to define the operations of our algebra. 
-/

/-
The operations in question are those you already know from CS1.
They include "not", "and", and "or", among others. The "not"
function takes a single bool value as an argument (it is a 
unary function) and returns its opposite bool value. The "and" 
and "or" operations each take two bool values (they are binary
operations) and return bool values. For example, as you should
already know, "true and false", an expression in which the and
function is applied to the two values, true and false, evaluates
to false in the algebra of Boolean truth values.
-/

/- *** MATHEMATICAL FUNCTIONS & THEIR COMPUTATIONAL REPRESENTATIONS *** -/

/-
Before getting to the definitions of these Boolean functions, we
address the more general notions of mathematical functions and of 
how we can represent mathematical functions as programs. In this part
of this course, we will represent mathematical functions as programs
in what we call a pure functional programming language, which is really 
just a machine-interpretable language of mathematical expressions.
-/

/-
In this section, we explain these concepts through a simple example.
We first consider the mathematical function, f(x) = x + 1, and then
we see how this function can be represented in a "computable" form 
program in the pure functional programming language of Lean. As you
will see, except for syntactic details and being precise about types, 
the program is really just the expression of the function itself! In
a pure functional language, programs are just mathematical expressions.
So here we go. 
-/

/-
Consider the function f(x) = x + 1. Mathematicians think of a function as
a set of pairs. Here those would be all of the (x, f(x)) pairs, where x is
any value of whatever type of numbers if being considered (let's assume x 
is any natural number, i.e., non-negative integer), and where for any such 
x, f(x) is the value of x plus one. This set of pairs has one element for
each natural number, including (3, 4) and (7, 8) but not (0, 0) or (7, 11). 

Mathematicians would write this set using "set comprehension notation", 
as f = { (x, y) | y = x + 1 }, which can be pronounced as "the set of 
all x-y pairs such that in each pair the y value in that pair is equal 
to the x value in that pair plus one." 
  
What is left implicit in this kind of "sort of formal" mathematics is the 
*type* of values over which x and y are allowed to range. Are the values of
x and y drawn from the natural numbers, the integers, the rationals, the
reals, the complex numbers, the quaternions? It's unclear. In everyday,
informal mathematical writing, mathemeticians expect the reader to know
the answer based on context. 

A mathematician seeking to be precise could instead write this: 
f = { (x: ℕ, y: ℕ) | y = x + 1 }. The "blackboard font" ℕ is standard 
mathematical notation for "the natural numbers". So this expression 
could be pronounced as "f is the set of x-y pairs where x and y range
over the natural numbers and where in each pair the y value is equal
to one more than the x value."

As an aside, mathematicians generally use the "blackboard font" symbol, 
ℤ, for the integers; ℚ, for the rationals; and ℝ, for the real numbers.
In Lean, you can obtain these symbols by typing \nat for the naturals,
\int for the integers, \rat for the rationals, and \real for the reals.
These strings get replaced with the symbols when they are followed by 
a space. Try it!
-/

/-
Whereas a mathematician generally thinks of a function as a set of
pairs, with one pair for each argument value for which the function
is defined. A programmer, on the other hand, thinks of a function as
a kind of machine that takes the first element of such a pair as an
argument, and that computes and returns the corresponding second
element of the corresponding pair in the mathematical definition
of the function. 

In other words, the programmer tends to represent a function as ... 
wait for it ... a program! 

When such a program is applied to an argument value (for x in our
example), the argument value is bound to the argument variable in
the body of the program, and the resulting program is evaluated 
yielding a result that is then returned to the caller. A program
thus says, "if you give me a value for x, I will hand you back
the corresponding value of y for the mathematical function in
question."

Here's how we'd express the function, f(x) = x + 1 in Lean, and how
we'd apply it to an argument value, 3, to reveale that (3, 4) is the 
pair in the mathematical function of interest with the x value of 3.
-/

def f (x: ℕ) := x + 1

/-
You can read this as saying "we define f to be a function that
takes one argument, x, of type ℕ, and that reduces to (returns)
that value plus one.
-/


/-
To apply a function, such as f, to a value, such as 3, you just
write the function name, here, f, followed by an expression for 
the argument value, here, 3. The result is what we call a function
application expression. In Lean, you can use the #reduce command to 
evaluate such an expression, i.e., to "reduce" the expression to the
value that it represents. Hover your mouse over the #reduce to see 
the result.
-/

#reduce f 3

/-
Lean provides a so-called "pure functional programming language." 
As already indicated, in such a language, a program is really just
the expression of a mathematical function. A function definition in 
such a language has a formal parameter (such as x) and an expression,
the "body" of the function, in which the formal parameter, x, can
appear. When such a function is applied to a value, such as 3, each 
occurrence of the formal parameter in the body is replaced by that 
actual argument value; the resulting expression is evaluated; and
the result is returned. 
-/


/-
In the example at hand (f 3), the function, f, is applied to the
value, 3. To evaluate (f 3), one takes the body of the function, f,
replaces each occurrence of x with 3 (here yielding the expression,
3 + 1) and evaluates the result to the compute the desired answer.
Note that the argument to a function can be any expression of the
right type. Here's an example.
-/

#reduce f (2 + 2)

/-
Just as in ordinary paper-and-pencil arithmetic, the inner expression,
involving the application of the + function the the arguments 2 and
2, is evaluated first. The result, 4, is then taken as the argument
to the outer function, f. 
-/

/-
EXERCISE: First predict then confirm your prediction of the return
value of the following (nested) function application expression.
-/

#reduce f (f (f 4))


/-
 *** THE FUNCTIONS OF BOOLEAN ALGEBRA ***
-/

/-
We now complete a definition of a limited version Boolean algebra
by defining several unary functions and binary operations over the
Booleans. A unary operation (aka function) takes one argument. A 
binary operation takes two. Let's start with unary operations.
-/

/- THE UNARY OPERATIONS OF BOOLEAN ALGEBRA -/

/-
A unary operation takes one argument and on the basis of its value
alone returns a result. Boolean operations take and return Boolean
values, here implemented (represented, if you will) as the value of
our type, bool.

The functions of an algebra are "closed" on the carrier set of that
algebra. What this means is that each such functions yields a result
in that set when given any argument values from that set. We can also
call such a function "total." A "partial function" is not necessarily
total, and a "strictly partial" function is definitely not total. An
example of a partial function on the real numbers is division. It is
not defined when the second argument (the denominator) is zero. 

We are interested in this section only in total unary functions on
the Booleans. What this means is, first, that for each Boolean value
there must be a corresponding Boolean result, and, second, to be a
*function*, there can be no more than one result. That is, there is
exactly one result for each argument value.
-/

/-
As a mathematical object, such a function is a set of pairs with
exactly one pair having each Boolean value in the first position.
For example, the set, { (tt, ff), (ff, tt) } is such a function. 
The set { (tt, tt), (tt,, ff) } is not, for two different reasons. 
First, it is not a function at all, because it has two pairs with 
the same first element, and so is not single-valued. Second, it
doesn't have a pair with ff as a first element and so is not total. 
-/

/-
We can graphically depict a total unary function on the Booleans
as a table with two rows and two columns. The first entry in each
row indicates the argument to the function, and the second entry,
the corresponding result. Every such table will have the same first
column, listing each and every possible argument value. Different
functions will then be defined by the corresponding entries in the
second column. Such a table looks like this, where underscores are
placeholders for return values. 

 Arg   Ret
+----+----+
| tt | __ |
+----+----|
| ff | __ |
+----+----+
-/

/-
One of the important concepts in discrete mathematics is that of
"counting" the number of objects of some particular kind. Here the
question is, how many unary functions are there on the Booleans?
The answer is equal to the number of different ways in which that
second column can be completed. For example, the co-called identity
function on the Booleans is the function where the return result
is always the same as the argument value. Here's the table.

 Arg   Ret
+----+----+
| tt | tt |
+----+----|
| ff | ff |
+----+----+

Of course such a table is just another way of representing the set
of pairs, { (tt, tt), (ff, ff) }, which is the right way to think of
the identity function as a mathematical object. If we wanted to give
this function a name, we might call it id_bool, with a prefix, id,
suggesting the identity function, and the suffix, _bool, suggesting
that this is the identity function for the bool type. 

If you were writing out the algebra in ordinary paper-and-pencil 
mathematics,  you'd write this function as id_bool(b) = b, where 
b is any Boolean value. You can imagine the corresponding identity 
functions for any other type. E.g., for the natural numbers, you 
could define id_nat as id_nat(n) = n, where n is any natural number.
-/

/-
We can now put all of these ideas together to write a pure
functional program that implements this function. We will call
this program id_bool. If we apply this resulting program to a
Boolean-valued argument value, b, which would be done by writing
the expression, "id_bool b", the result that is returned will be
just b itself. 

As we've now seen, a Boolean function can be represented in at
least three ways:

- as a set of pairs, such as { (tt, tt), (ff, ff) }
- in the form of a table, namely a truth table
- using an equation, such as "id_bool(b) = b" 
  
Simple pure functional programs are generally written in the
equational form. Here's the code for the id_bool function. 
-/

def id_bool (b: bool) : bool := b

/-
The "def" keyword introduces a new definition -- a binding of a name,
or "identifier", here id_bool, to a value, here a definition of the
identity function that takes a bool argument and returns that same
value as the result. (Yes, function bodies are values, too.)

You can thus pronounce this code as follows: "we define id_bool to 
be a function that takes one argument of type bool, bound to the 
identifier b,  and that also returns a value of type bool, namely 
that obtained by evaluating the expression, "b", in the context of
the prevailing binding of the identifier, b, to the value of the
bool argument to which the function is applied in any given case. 
-/


/-
EXERCISE: Write pure functional programs called false_bool and
true_bool, respectively, each of which takes a bool argument and
that always returns false or true, respectively.
-/

-- TYPE INFERENCE

/-
There's a shorter way to write the same function: we can leave out 
the explicit return type (the bool after the colon) because Lean 
can infer what it must be by analyzing the type of the expression
that defines the return result. The argument, b, is declared to
be of type bool, so it is clear that type obtained by evaluating
the expression, b, defining the return result, is also of type bool. 
Here's another version of the same definition,  with a "prime" mark 
to make the name unique, exhibiting the use of type inference.

-/

def id_bool' (b: bool) := b

/-
EXERCISE: Use type inteference to write shorter versions of 
you true_bool and false_bool programs.
-/

-- FUNCTION APPLICATION EXPRESSIONS

/-
A function application expression is an expression written 
as a function name (or more generally as an expression that
reduces to a function value)) followed by an expression that 
reduces to a value that is taken to be the argument to the 
function. 

The simplest form of a function application expression is
just a function name applied to a so-called "literal value"
of the required type. In the function application expression,
"id_bool tt", you see first a function name, the "variable",
id_bool, followed by the literal expression, tt.

Here's an example in which id_bool is
applied to the literal value, tt. By hovering over the
#reduce command, you can see the value to which this
function application expression is reduced.
-/

#reduce id_bool tt

/-
EXERCISES: Write and reduce expressions in which you apply
your true_bool and false_bool programs to each of the two
bool values, thereby exhaustively testing each program for
correctness.
-/

-- EVALUATION OF FUNCTION APPLICATION EXPRESSIONS

/-
Reducing a function application expression is a very simple
process. First you evaluate the function expression, then you
evaluate the argument expression, then you apply the resulting
function to the resulting value. Let's do this in steps. 

First, the function expression is given by the identifier,
id_bool. To obtain the actual function, Lean looks up its
definition and finds a function that takes a bool as a value
and that returns that same bool value as a result.

Second, the identifer, tt, is a literal expression for the
tt value/constructor of the bool type.

Finally, the function is applied to this argument value.
This is done by substituting the argument value for the
argument variable wherever it appears in the body of the
function and by then evaluating the resulting expression.

The body of the function in this case is just "b". So the
value, tt, is substituted for "b". Finally this expression
is evaluated, once again producing the value, tt, and that
is the result of the function application!
-/

/-
EXERCISE: We previously confirmed that the definition of 
tt is ambiguous in the current environment. So why was it 
okay here to write tt without qualifiers in the expression, 
id_bool tt?
-/

/-
EXERCISE: Explain in precise, concise English exactly 
how your true_bool program is evaluated when applied to
the argument given by the literal expression, tt.
-/


-- FUNCTION TYPES

/-
Functions also have types. We can check the type of id_boolean 
using the #check  command. Hover your mouse over the #check. 
Lean reports that the type of this function is boolean → boolean. 
That is how, in type theory, we write the type of a function
that takes an argument of type bool and that returns a result
of that same type. 
-/
#check id_bool

/-
EXERCISE: First mentally determine the types of your false_bool
and true_bool functions, and then use #check commands to test
your predictions.
-/

-- TESTING FUNCTION IMPLEMENTATIONS FOR CORRECTNESS

/-
Whenever we write programs that are meant to compute values
of functions for given arguments, the question arises, did
we represent/implement the intended function correctly?  

An important observation is that the question presumes
that we have a definition of a function to be implemented
against which the correctness of the implementation can
be evaluated. 

Consider our implementation of id_bool? Against what 
specification should its correctness be determined? 
Here the best answers are that we can evaluate the 
correctness of id_bool against either the truth table 
or the equivalent set-theoretic definition. The tuples 
in the definition of the function, (tt, tt) and (ff, ff), 
tell us what result to *expect* for each argument value: 
expect tt when given tt as an argument and expect ff 
when given ff as an argument.
-/

/-
The process of software *testing* is one in which a
program is evaluated for one or more argument values
and the actual results are compared with the expected
results to identify any discrepancies. A single pair,
(argument value, expected result) is called a *test
case*. The tuples in our set-theoretic definition
of id_bool can thus serve as test cases. Consider
the tuple, (tt, tt). Viewing it as a test case tells
us that we should expect that "id_bool tt = tt." 
-/

-- PROPOSITIONS AND PROOFS

/-
A claim like this---an assertion that a certain state
of affairs holds in a given situation, here the assertion
that if we evaluate id_bool with argument tt the result 
will be tt---is what in logic we call a proposition. 

A proposition is a truth claim. A proposition can thus
be true, or false, or, in some logics the truth of a 
given proposition can be indeterminate. In any case, 
establishing the truth of a proposition requires what
we call a proof.
-/

/-
The real power of Lean is that in addition to letting
us write programs, it also let us write propositions
and proofs, and it checks that proofs are correct.
Here, the proposition for which we want a proof is
the proposition, id_bool tt = tt. We can write and
prove this proposition in Lean as follows.
-/

theorem id_bool_correct_for_tt: id_bool tt = tt :=
    rfl
/-
We introduce a proposition and its proof with the
keyword, theorem. Technically theorem is just the
same as definition: it's a way to say we're about 
to define a value but we intend for that value to
be a proof of some proposition 

Following this keyword we give a name to the proof 
that we intend to define: id_bool_correct_for_tt.

Next, after the colon comes the proposition itself:
here, id_bool tt = tt. 

Next comes a :=. Finally we write the proof: here 
the cryptic term, rfl. 
-/

/-
PROOF BY SIMPLIFICATION AND THE REFLEXIVE PROPERTY
OF EQUALITY
-/

/-
Proofs come in many forms. As a mathematician,
you learn what forms of proofs work for what
kinds of propositions. Here we have propositions
that two expressions reduce to the same value.
To construct such a proof, you first reduce each
expression to a value. The expression id_bool tt
reduces to tt. The expression tt reduces to tt 
(it's alrady reduced to a value). Then what 
you have is the proposition, tt = tt. But 
that is true by the reflexive property of
equality: for any value x, no matter what it 
is, x = x. So tt = tt. The proposition is
thus proved.
-/

/--/
You thus read "rfl" as saying what a mathematician
would pronouce as, "by simplication of expressions 
and the reflexive property of equality." 

The fact that Lean accepts rfl as a proof (value)
provides a very strong mechanized check on the 
correctness of the proof.
-/

/-
EXERCISE: Use Lean to state and prove the proposition
that id_bool ff = ff.
-/

/-
EXERCISE: Write a similar definition, bad_proof_1,
asserting that there is a proof of the proposition,
id_bool tt = ff. Does Lean accept the proof? What 
error messages does Lean report?
-/

-- YOUR WORK HERE

/-
The red under rfl indicates a "type mismatch", stating
that rfl was expected to be a proof that something
(here given the arbitrary name m_2) is equal to itself,
but that (in so many words) the things asserted to be
equal are not equal. 

The red under bad_proof states, in effect, that the
name, bad_proof, was expected to be bound to a proof
of some proposition, but it is not so bound (due to
the preceding error).

A proposition that is false has no proof. To see that
rfl cannot be a proof of id_bool tt = ff, observe that
id_bool tt reduces to tt, so the proposition reduces 
to tt = ff, but tt and ff are not equal, and so rfl is
not a valid proof: it can only be used to prove that
two values are equal to themselves. In the logic of 
Lean, different constructors *always* build different 
values -- values that are never equal to each other --
so ff cannot be equal to tt. The proposed proof, rfl,
is thus rejected. 
-/


/-
EXERCISE: Give a proof, call it one_equals_one, for 
the proposition, 1 = 1.
-/

-- YOUR WORK HERE

/-
EXERCISE: Attempt to give a proof, using rfl, of the
proposition that 1 = 2. What happens. Investigate and
briefly explain in plain English the meanings of the
error messages that are reported.
-/


/- UNIVERSAL QUANTIFICATION AND PROOF BY CASE ANALYSIS -/

/-
Testing that a program is corect for one input, which is
what a test case asserts, does not prove that it is correct
for all possible inputs, unless there is only one possible
input, in which case the function is pretty much useless.
The kind of propositions that we really want to prove are
ones that claim= a program is correct *for all* possible
inputs. 
-/

theorem id_bool_correct: 
  ∀ b: bool, id_bool b = b 
    | tt := rfl
    | ff := rfl




/-
We once again give our proof a name that reflects the 
proposition that it proves: here, id_bool_correct. We
are claiming that the function is correct for every
possible input. On the second lines is the proposition
itself. The "universal quantifier", ∀, pronounced as
"for all", or "for every", or "for any". It is followed 
by a variable, b, and its type, bool. So far we can thus
pronounce the proposition as saying "for any value, b, 
of type bool." Then comes a comma followed by the rest
of the proposition: namely, the claim that, for any
such b, id_bool b = b. The "b" in this part of the 
proposition is the b "bound" in the quantifier part 
of the expression. The whole proposition thus covers 
all possible cases, and reads, "for any boolean value,
b, id_bool b is equal to b." 

We can't use rfl directly as a proof, because the 
form of the proposition is not a simple assertion
of equality of the values of two expressions. It is
instead a "universall quantified" proposition

The remainder is the code instead gives a "proof by 
case analysis." We show that for each possible value
of b considered in turn, the claim that id_bool b = b
is true. 

Because there are only two values of type bool, there 
are two cases: one where b is tt, and one where b is 
ff. 

Each case starts with a vertical bar, followed by the 
case (the value of b) being considered. Then comes a
:=, and followed by a proof for that case. 

Consider the first case, in which b is bound to tt. 
In this case, making this subsitution in the "body"
of the proposition gives us id_bool tt = tt. For 
this proposition, we already have a proof! It's rfl.
The same holds true for the second case. 

As we've now given a proof for each individual case, 
we've given a proof "for all" cases, showing that
the overall quantified proposition is true. Proving
universally quantified propositions about software
correctness is called formal verification, and is a
state of the art approach to producing ultra-high
quality code. Such a high standard of correctness
is not always necessary or practical, but when 
lives or nations depend on correctness of code, it
is a "gold standard" approach to software quality. 
-/

/-
EXERCISE: In a similar style, state and prove the
proposition that every natural number, n, is equal 
to itself. Call your proof nat_refl. You can get
the ∀ character (the universal quantifier, for all)
in Lean by typing \forall followed by a space.

NOTE: You don't know how to write such a proof 
yet, so just write "sorry" instead. This tells
Lean to accept the proposition as being true
even though you haven't yet given a proof (and
even if it's actually not even true). You are
saying, "accept the proposition without proof",
or "accept it as an "axiom." An axiom is any
proposition that is accepted without a proof.

This is really just an exercise that asks you
to write a proposition in Lean using a ∀.
-/

-- theorem nat_refl: ∀ n: nat, n = n := sorry

/-
EXERCISE: State a proposition and give a proof
in Lean for the proposition stating that for
*every* possible argument, b, to false_bool,
false_bool b = false. Similarly prove that
your implementation of true_bool is correct
with respect to our understanding of how it
should behave.
-/



/-
Exercise: How many test cases do we need to "prove" that 
the function works correctly for all possible inputs of 
type boolean. (Hint: how many such inputs are there?) 
Write any additional test cases need to prove that our 
definition of the identity function works as we expect 
it to. 
-/

/-
Proof by case analysis often works well when you want to 
prove that something is true for every element in a finite 
set of elements. It isn't an appropriate proof strategy when 
the set of values to be considered is infinite, as it would 
be impossible to test every individual case. For example, 
you can't prove that a functional program that takes a 
natural number as an argument is correct by giving a proof
for each natural number in turn because there is an infinity
of such values. Another proof strategy would be need. It 
goes by the name of "proof by induction." More on that later!
-/

-- THE MAJOR FUNCTIONS OF BOOLEAN ALGEBRA

/-
So far we have implemented three of the four unary functions
of Boolean algebra. The remaining one is usually called "not"
or "negation." We will give it the name, negb. Given one of 
the two Boolean values as an argument, negb returns the other.

The set-theoretic definition is negb = { (tt, ff), (ff, tt) }.
The truth table depicts this definition graphically. 

 Arg Ret
+---+---+
| T | F |
+---+---|
| F | T |
+---+---+
-/

/-
We don't yet have the tools needed to implement this function.
The tool we need is called pattern matching. It's just a form
of case analysis! Here's the code.
-/

def negb (b: bool): bool :=
  match b with 
    | tt := ff
    | ff := tt
  end

/-
We define negb to be a function that takes a Boolean value and
returns a Boolean value. That is, the type of this function is,
like the others we've defined so far, bool → bool. The thing that
is different about this function is that we have to inspect the
argument value to determing what result to return. We do that by
case analysis! What the body of this function says is "match the
value of b with each of its possible cases. THe first case is tt,
and in this case (after the :=), the return value is given by
the expression ff. Similarly, for the case, ff, the result is tt.
There are no more cases, and so this function has given a result
value "for every" possible value of b. This is thus a definition
of a total function by case analysis!

(You get the → symbol in Lean by typing \to. EXERCISE: Try it.)
-/

/-
EXERCISE: Write a second implementation of id_bool, call it
id_bool', using case analysis. Prove by case analysis that it 
is correct with respect to its expected behavior.
-/

-- FUNCTION TYPES

/-
In Lean, every function is required to be total. That is, a
function must define how to construct a return value of the
specified type "for every" value of its argument type. The
four unary functions we've seen so far all do this. For every
value of type bool, each of them returns a value of type bool.
We've seen that you can write this type as bool → bool, but
another way to write it is, ∀ b: bool, bool. This just says,
for every value of type bool you can give me, I promise to
give you back a value of type bool. Hover over the #check
that follows. You will see that we have just found two ways
to write the same function type.
-/


#check ∀ b: bool, bool

/-
EXERCISE: Use a universal quantifier to write and check the
type of functions from natural numbers to bools. An example
of such a function would be one that took any natural number
and returned tt if and only it it was even, and ff otherwise.
-/

#check ∀ n: nat, bool

/-
THE BINARY OPERATORS OF BOOLEAN ALGEBRA
-/

/-
Binary operations of an algebra are functions that take two 
arguments of a given type (such as bool) and that return a
value of that same type. The conjunction, aka and, operation
in Boolean algebra is an example. It takes two Boolean values
as arguments and returns a Boolean result. If both arguments
are true, its result is true, otherwise it is false. This
behavior is reflected in  the following set-theoretic and 
truth table specifications. We will call the function andb. 


andb = { ((T, T), T), ((T, F), F), ((F, T), F), ((F, F), F) }

Note that we again give the function as a set of argument/result
pairs, but now each argument is itself a pair of values.



A truth table view:

    andb
+---+---+---+
| T | T | T |
+---+---|---+
| T | F | F |
+---+---+---+
| F | T | F |
+---+---+---+
| F | F | F |
+---+---+---+
-/

/-
We already have all the tools but for one to implement this
function. The one tool we need is pattern matching (i.e., case
analysis) for *pairs* of argument values. This following code
shows how to do this. Instead of matching on one value, b, we
now match on the comma-separated pair of values, b1, b2; and
each case now corresponds to a possible pair of argument values.
There are four possible pairs of Boolean values, and so there 
are four cases to consider. Note how the visual organization
of the code reflects the truth table contents (and thus the
equivalent set-theoretic definition nearly directly.)
-/

def and_boolean' (b1 b2: bool): bool :=
    match b1, b2 with
        | tt, tt := tt
        | tt, ff := ff
        | ff, tt := ff
        | ff, ff := ff
    end

/-
It's often the case (ha ha) that in a case analysis, one
case stands out and several others or all the rest can be
considered at once. To define "andb" all we really have to
say is "if b1 and b2 are both true, the result is true, and
in any other case the result is false." In Lean and in many
other functional programming language, we can write cases
analysis using "wildcards" (here underscores) that match
any values not considered in previous cases.
-/

def and_boolean (b1 b2: bool): bool :=
    match b1, b2 with
        | tt, tt := tt
        | _, _ := ff
    end


/- 
EXERCISES:

1. Using case analysis, write definitions of the following binary 
functions on booleans in the form of (a) sets, using display notation, 
(b) truth tables, (3) functional programs. When writing functional
programs, use wildcards where possible to shorten your definitions.

* or (call it orb)-- false if both arguments are false, otherwise true
* xor (xorb) -- true if either not both both arguments are true
* nand (nandb) -- the negation of the conjunction of the arguments
* implies (implb) -- false if b1 is true and b2 is false otherwise true
* nor (norb)-- the negation of the "disjunction" of its arguments

2. By the method of case analysis, prove that your "or" and "xor" programs are
correct with respect to your truth table definitions, i.e., that they produce the
outputs specified by the truth tables for the given inputs.

3. How many binary functions on booleans are there? Justify your answer. Hint:
think about the truth tables. The set of possible arguments is always the set of
pairs of booleans. How many different ways can these arguments be associated with
boolean results?

4. Write a second definition of nandb, call it nandb', that instead of
using pattern matching applies a combination of andb and negb functions.
Surround function application expressions with parentheses to specify
groupings when they might otherwise be misinterpreted, e.g., vvv (www x y)
in the case where the argument to vvv is meant to be the result of 
evaluating www x y.
-/


/-
FORMAL AND INFORMAL PROOFS.
-/

/-
Our formal proofs are very precise and their correctness is assured by Lean's
automated proof checking mechanism. By contrast, most working mathematicians
write informal proofs. These are still highly precise, but they are written in
structured English (or another natural language) rather than in what amounts 
to code. The major benefit of informal proofs is that they are easier for most
people to understand. The downside is that mistakes in proofs can, and often 
do, go undetected. One benefit of formal proofs is that they are checked for
correctness by a computer, and, when verified can be accepted as correct with
very high levels of confidence. Another benefit of learning how to write such
proofs is that the relationships between forms of propositions (e.g., equality
claims or universally quantified claims) and the forms of the corresponding
proofs becomes very clear. Learning how to write both informal and formal
propositions and proofs is an important goal of this class.
-/

/-
As an example, let's recast our formal proof of the correctness of our
program for id_bool as an informal proof. Here's how it might be written.

"The goal is to show that for every value, b, id_bool = b. We do this by
case analysis. There are two cases: b = tt, and b = ff, respectively. We
first consider the case where b = tt. In this case, the proposition to be
proved is that id_bool tt = tt. We prove this by simplification of the left
hand side to tt by applying the definition of id_bool. What's left to prove
is that tt = tt, and this is done trivially by appealing to the reflexive
property of equality. The proof of the second case is by the same strategy
of simplification and reflexivity of equality."
-/


/-
EXERCISE: Write both a formal and a corresponding informal proof of the 
correctnes of your andb function.
-/

/-
BOOLEAN ALGEBRA AS AN ALGEBRA
-/

/-
We have now gotten to the point where we can make sense of the term, boolean algebra.
Boolean algebra is an algebra, which is to say it is a particular set of values and
a particular collection of operations closed on that set. We have represented the set
of values as a type, namely our bool type. We have represented the operations as pure
functional programs taking and returning values of this type. 

Moreover, by defining this set and its operations in a namespace, we've grouped
the values and operations on them in a meaningful way.

+ -----------+
|  csdm.bool |  DATA
+------------+
|  csdm.negb |
|  csdm.andb | OPERATIONS
|  csdm.orb  |
|     ...    |
+------------+

Such a structure, comprising a data type and a collection of operations on it is
also known, in the computer science field, as an "abstract data type (ADT)". When
computer scientists talk about "types", sometimes they mean inductively defined
types, such as the bool type (separate from operations), and sometimes (actually
more often) then mean abstract data types. Abstract data types, i.e., algebras!,
are fundamental building blocks of software. It took a while for us to build up
our bool ADT, but now that we're done, you can step back and now view our data 
type definition and our definitions of a collection of associated operations as 
a coherent whole, an abstract data type that implements the algebra of Boolean
truth values. 
-/

-- USING AN ABSTRCT DATA TYPE

/-
The last question we address in this chapter is how to use such an abstract 
data type implementation. To this end, please open and shift your attention
to the file csdm_bool_test.lean. It will show you how to import and use type
and function definitions in another file: this file in this case. 
-/

/-
SUMMARY

- boolean algebra
  * inductive definition of the type of booleans
  * functions on booleans
  ** set theoretic, truth table, and pure functional representations
  ** unary functions on booleans
  ** binary functions on booleans
- types and values
- inductive definitions
- tuple values and tuple types
- relations and functions (set theoretic)
- functional programs: their types and values
- propositions
  * about equality of terms
  * universally quantified propositions
- an application: propositions and proofs of program correctness
- proof strategies:
  * by simplification and reflexivity of equality
  * by exhaustive case analysis
- formal and informal proofs
- algebras
-/


end csdm