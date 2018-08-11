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
Picking good names for concepts is important in every field.
It's  especially important in computer science and software
development because we want complex "code," often involving 
hundreds, thousands, or even millions of identifiers (the
CS term for a name to which a meaning is given in a program), 
to be humanly understandable.

For example, rather than using a cryptic identifier, such as
"n", to refer to the "next node" to be processed in a loop,
one might instead use the identifier "next_node". It makes
no difference to the machine, but it makes a big difference
to the programmer coming to the code for the first time or
returning to it after some time has passed. The names that 
we pick in this way can serve to document the intended 
interpretation of the otherwise cryptic logic of the code.

A problem arises, of course, when two programmers, working
on two different parts of a larger program, decide to use
the same name for different concepts. One can imagine two
programmers both deciding to use "next_node" to refer to
the next object to be processed in two unrelated pieces of
code. When those pieces of code are brought together, the
result could be that the name becomes ambiguous: with two
different meanings.

A general solution to this problem empoyed by many
different programming languages is to define meanings
for identifiers within different namespaces. A namespace
is just a prefix that it implicitly prepended to each
name defined within the namespace. 

If you've programmed in Python, Java, or most any other
industrial programming language, then you've seen the 
use of namespaces.

In this class, we will enclose all of our definitions 
within a namespace called edu.virginia.cs.dm. The idea
is that (1) the namespace explains the context in which
names are defined, i.e., the discrete math (dm) class
at UVa; and (2) no one else seems likely to pick the 
same namespace. The next line of code tells Lean that
all names between here at the "end edu.virginia.cs.dm"
command at the end of the file are defined within the
edu.virginia.cs.dm namespace.
-/

namespace edu.virginia.cs.dm

/-
What this means is that every name, such as xbool, 
below is implicitly prefixed with edu.virginia.cs.dm. 
The "fully qualified" name for xbool as defined below 
is thus edu.virginia.cs.dm.xbool. 
-/

/-
With that ancillary detail out of the way we can now turn to the
main content of this chapter, giving our own implementation of 
Boolean algebra. 
-/


/-
**** INDUCTIVE DEFINITIONS OF TYPES: CASE STUDY OF bool ****
-/

/-
Our implementation comprises (1) a definition of the "carrier 
set" of values of the Boolean type, and (2) a definition of a 
set of operations (functions) closed on this set. 

We first specify the "carrier set" of values of Boolean 
algebra. The values are typically called true and false
(with different names in different natural languages).
The set of values of Boolean algebra can thus be written 
as { true, false }. We call this "display notation".

A data type defines nothing other than a set of values, 
namely the values that are specified as having that type 
and no other values whatsoever. 

Here's how we will represent the carrier set of Boolean
algebra as a data type in the Lean language. We explain
this code below.
-/

inductive xbool : Type
| xff : xbool
| xtt : xbool

/-
In Lean, as in many other functional languages, we define types
inductively. We specify the name of the type and then we give a
list of constructors that specify the values of the type being
defined.

The Lean keyword "inductive" introduces an inductive definition.
The name of the type being defined is xbool, which is declared to
be a type. Finally a list of constructors is given, each starting
with a vertical bar, followed by the name of the constructor and,
at least in the simple case here, a statement saying that the given
constructor *is* a value of the type being defined. 

We have thus just defined a type called xbool with two values,
and no other values, namely xtt and xff. Our intended interpretation
is that xbool represents the carrier set of Boolean algebra, xtt
reprents the true value of Boolean algebram and xff represents 
the false value.

This definition precisely mirrors the definition of the built-in
Boolean type in Lean, which is specified like this:

inductive bool : Type
| ff : bool
| tt : bool

We have prefixed each name in our version of Lean's bool type 
with an x to avoid confusing conflicts with the names of the
built-in types and constructors. Why, you might ask, do we
do this, given that we're within our own namespace? That's a
good question. The answer is that even with use of namespaces,
there is still some complexity and potential for confusion we 
don't want to burden you with in this class.
-/

/-
Our inductive type definition has actually defined meanings 
for three different names: xbool, xtt, and xff. The name, or
identifier, xbool, now refers to a type with two values, xtt
and xff. Each xtt and xff refer to two different constructors
that in effect define the two different values of the xbool
type.

We can use Lean's #check command to see that these names are
defined, and Lean will tell us the type of thing that each
name means. We start by using the fully qualified name of
our xbool type. Hover your mouse pointer over the two
parts of this command to see what it tells you.
-/

#check edu.virginia.cs.dm.xbool

/-
Because we are within the edu.virginia.cs.dm namespace here,
and because there is no ambiguity, we can leave off the whole
edu.virginia.cs.dm prefix. Note that when you hover over xbool
in the following #check command, it does tell you the fully
qualified name of xbool.
-/

#check xbool

/-
Importantly, Lean tells you that the type of xbool is Type.
That's it's way of saying "xbool is a type!"
-/

/-
You might think that you can also use the #check command
to check to see what's the type of xtt, and indded we can.
However, we can't just do "#check xtt" because the name,
xtt, is defined in a namespace created by the xbool type.
Uncomment the following code and see what error you get.
-/

-- #check xtt

/-
Here's what you need to do instead.
-/

#check xbool.xtt

/-
This is of course equivalent to the following.
-/

#check edu.virginia.cs.dm.xbool.xtt

/-
What we see is that the name, xbool, as defined in the
current namespace, is "visible" in this namespace, but
the names defined in its namespace are still hidden away.

If you want to be able to use the names xtt and xff 
without qualifiers, you have to "open" the namespace 
in which they are defined, i.e., the xbool namespace.
-/

open xbool

/-
Ah, now it all just works. That's it on namespaces.
-/

#check xtt
#check xff

/-
We've thus got the first component of our algebra defined: the 
carrier set of Boolean values! To complete our implementation, 
we need to define a set of operations on this set: operations 
such as "and", "or", and "not", which should already be familiar 
from CS1. Take a few minutes to recall exactly how they work in
a language you already know (e..g, Python).
-/

/-
EXERCISES:

* Assign the Boolean value, true, however it is written in
your favorite language, to a variable called X. Assign the
Boolean variable, false, to Y. Assign to a variable, Z, the
value of the negation of ("not") X. Assign to W the disjuction
("or") of X and Y. Finally print the value of the conjunction
of W and true. What value is produced?
-/


-- MATHEMATICAL FUNCTIONS AND PURE FUNCTIONAL PROGRAMS

/-
As you now recall from CS1, "and", "or", and "not" are really
just functions that take and return Boolean values. The "not"
function takes a single bool value as an argument ("not" is a 
unary function) and returns its opposite bool value. The "and" 
and "or" operations each take two bool values (they are binary
operations) and return bool values. 
-/

/-
Before seeing how to implement these Boolean functions in Lean, we
address the more general notions of mathematical functions and of 
how we can represent ("implement") mathematical functions as programs. 
In particular, we will implement mathematical functions as programs
in thepure functional programming language of Lean, which, as we 
will see, is really just a language for writing mathematics in a 
that that supports computerized "sanity checking" and evaluation.
-/

/-
Consider the function f(x) = x + 1. Mathematicians think of a function 
as a set of pairs. If you were to graph this function, the resulting
line would pass through each and every (x, f(x)) pair in this set.
This set of pairs has one element for each x, including (3, 4) and 
(7, 8) but not including (0, 0) or (7, 11). 

Mathematicians would typically write this set using what we call
"set comprehension notation": f = { (x, y) | y = x + 1 }. Here f
is the name of the function and the set is defined to be "the set of 
all x-y pairs where the y value is equal to the x value plus one." 
  
What is implicit in this kind of semi-formal mathematics is the 
*type* of values over which x and y range. Are the values of x and 
y drawn from the natural numbers (the non-negative integers from
zero on up), the integers (including negative whole numbers), the 
rationals, the reals, complex numbers? In ordinary, semi-formal
mathematical writing, mathemeticians expect the reader to be able
to infer the answer based on context. Here for example, most high
school mathematicians would assume that x and y range over the
reals.

A mathematician seeking to be more precise could instead write this: 
f = { (x: ℕ, y: ℕ) | y = x + 1 }. The "blackboard font" ℕ is standard 
mathematical notation for "the natural numbers". So this expression 
could be pronounced as "f is the set of x-y pairs where x and y range
over the natural numbers and where in each pair the y value is equal
to one more than the x value." So in this function we have the pair
(2, 3) but not the pair (2.5, 3.5), because 2.5 and 3.5 are not even
possible values for x and y. They are of the wrong type.

As an aside, mathematicians generally use the "blackboard font" symbol, 
ℤ, for the integers; ℚ, for the rationals; and ℝ, for the real numbers.
In Lean, you can obtain these symbols by typing \nat for the naturals,
\int for the integers, \rat for the rationals, and \real for the reals.
These strings get replaced with the symbols when they are followed by 
a space. Try it!
-/

-- REPRESENTING FUNCTIONS AS PROGRAMS THAT COMPUTE FUNCTION VALUES

/-
Whereas a mathematician generally thinks of a function as a set of
pairs, with one pair for each argument value for which the function
is defined, a programmer, on the other hand, thinks of a function as
a kind of machine that takes the first element of such a pair as an
argument, and that computes and returns the corresponding second
element. For example, if implement the function f(x) = x + 1 as a
program, let's also call it f, then we could write and evaluate the
expression f(3) and the machine would compute and return the value
4. A program thus says, "if you give me a value for x, I will hand 
you back the corresponding value of f(x). The program implicitly
thus represents the set of pairs of the desired function. 
-/

/-
Here's one way to express the function, f(x) = x + 1 in Lean.
-/

def f (x: ℕ) := x + 1

/-
We start with the keyword, def, for "definition." The comes the 
name we're defining, f, following by names for and the types of
arguments it takes, then a :=, followed by the expression that
defines what value the function returns for any given value of
x.
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


-- EVALUATING (REDUCING) FUNCTION APPLICATION EXPRESSIONS


/-
Lean is a so-called "pure functional programming language." 
As already indicated, in such a language, a program is really just
the expression of a mathematical function. A function definition in 
such a language has a formal parameter (such as x) and an expression,
the "body" of the function, in which the formal parameter, x, can
appear (as it does in the expression, x + 1, for example). 

When such a function is applied to a value, such as 3, the
resulting expression is evaluating by substituting the actual
value (here 3) for every occurrence of the argument (here x)
in the function body (here x + 1). The resulting expression 
(here 3 + 1) is itself then evaluated. Finally the resulting 
value is returned. That value is the result of "reducing" the
original function application expression. 
-/

/-
Note that the argument to a function can be any expression that
itself reduces to a value of the right type. Here's an example.
-/

#reduce f (2 + 2)

/-
Here we're using Lean's built-in addition function applied to the
two arguments, 2 and 2, to represent the value to be passed as the
argument to f. 

Just as in ordinary paper-and-pencil arithmetic, in Lean, he inner 
expression (2 + 2) is evaluated first and result, 4, is then taken 
as the argument to the outer function, f. 
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