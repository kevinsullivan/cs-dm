/-
Return to your earliest days of high school algebra and 
consider the simple function f(x) = x + 1. Reflect on how 
do you think about it? 

* Do you first see a graph in your mind -- a line rising 
from left to right at a 45 degree angle and crossing the 
y-axis at the point y = 1? 

* Do you think of the function as a set of ordered pairs,
namely all the pairs in which the second number is equal
to the first number plus one?

* Do you think of the function as a kind of "machine", 
one that, when given a value for x hands you back a value
for f(x)? E.g., as a machine that when given an argument
value of 3 returns a result value of 4?

These are all perfectly wonderful ways to think about,
and indeed, to represent such a function. The first two
ways, as a graph and as a set of pairs, are closely 
related: the graph is simply a drawing in which each
ppossible air of values is represented as a point in 
the Cartesian plane and where the pairs constituting 
the function are highlighted in pencil. The result is
a continuous line infinite in extent hitting all and
only the pairs in the set of pairs for the function, f.

The view of the function as a kind of abstract machine 
is different. Whereas the first two views explicitly
represent the set of pairs making up the function, the
machine view implicitly represents this set of pairs.
The machine says, "if you give me the first element
of such a pair, I will give you back the second one."

Mathematicians think of functions as sets of pairs.
Programmers tend to think of functions as machines.
Indeed when functions (viewed as sets of pairs) are 
implemented as programs, those programs do serve as 
machines that automatically compute function values:
if you give the machine a 3 (by applying the program
to the argument, 3) it returns 4, and more generally,
if you give it some value, x, it returns the value,
x + 1!
-/

-- FUNCTIONS AS SETS OF PAIRS
/-
Mathematicians think of a function most fundamentally 
as a set of pairs. In paper-and-pencil mathematics, a
mathematician might denote such a set using what we
call "set comprehension notation." Here's what this
would look like: 

     f = { (x, y) | y = x + 1 }. 
     
Here f is the name of the function and the set is 
defined to be "the set of all x-y pairs where the 
y value is equal to the x value plus one." 

We can represent the function this way in Lean, as
well, using what we call set comprehension notation, 
as follows:
-/


def f := { p: ℕ × ℕ | p.2 = p.1 + 1 }

/-
This can be read as saying, "We define f to
be the set of values, p, where each such p 
is a pair of natural numbers, such that the 
second component of the ordered pair, p, is 
equal to the first component plus one.
-/

/-
We now take a few paragraphs to drill down
on some details.

First, here's more about math in Lean.
The #check command in Lean will tell us the
type of an object. Checking the type of f
reveals that it is indeed a set of pairs of
natural numbers. Hover your mouse pointer
over the #check command. The message you
get back says that the type of f is what
you can read as "set of values, the type
of which is "pair of natural numbers."
-/

#check f

/-
We can denote specific pairs of natural 
numbers as ordered pairs using ordinary
mathematical notation. Here we assign the
pair, (3, 4), as the value of goodPair
(an identifier, or variable name, that
we just made up).
-/

def goodPair := (3, 4)

/-
Lean confirms that the type of goodPair
is ℕ × ℕ, which is to say, the type whose
values are the pairs of natural numbers.
Carefully compare the type of f with the
type of goodPair. The former is a set of
pairs. The latter is a specific individual
pair.
-/

#check goodPair

/-
We can access the elements of pair by
writing .1 or .2 after the pair, to get
its first or second element respectively.
The #reduce command takes and expression
and reduces it to the value it represents.
Hover your mouse over the #reduce to see
the result.
-/

#reduce goodPair.1
#reduce goodPair.2

/-
EXERCISE: Define badPair to be the pair
of natural numbers, (3, 3). We call it a
bad pair because it's not a pair in f.
Use #check to check its type and use
#reduce and .1 and .2 (the first and 
second projection functions) to confirm
that both elements of the pair are 3.
-/

/-
So there you have it. We have defined
the function f declaratively as a set
of pairs. Declarative, "set-theoretic" 
definitions of functions are ubiquitous 
in mathematical writing and reasoning.
-/

/- 
One of the advantages of this style of
specification is that it is expressive. 
We can say *what* the relationship is
between the arguments to and results of
a function without having provide a
procedure for compute results given 
arguments. 

Here for example is a declarative 
specification of the square root function 
for natural numbers. This function contains
pairs of natural numbers where the second
element of each pair is the square root
of the first. Examples include (1, 1), 
(4, 2) and (9, 3), but not (9, 4) or
(8, 2). 
-/

def sqrt_nat := { p: ℕ × ℕ | p.2 * p.2 = p.1 }

/-
The pairs, (9, 3), (4, 2), and (1,1 ) are in 
this function, but (9, 4) isn't because it is
not the case that 9 = 4 * 4.
-/

/-
This specification is crystal clear. It
really says what it means to be a square
root: that result times itself has to be
equal to the argument the the function.

By contrast, a Python program to compute 
natural roots of natural numbers would 
not be anywhere near as expressive. It might
for example use a loop to check each number,
n, between zero and an argument, a, to see 
if n * n is equal to a, returning n if it
satisfies this condition, or an error if it
can't find such an n. Just looking at such
code would hardly make it clear what the
code is meant to do.
-/

/-
A second advantage of the declarative style
of specification is that it let's us specify
*partial* functions without having to explain
anything about values on which a function is
undefined.

Consider the argument 8, for example. There is
no natural number, n, such that n * n = 8. So
there is no pair in this function with first 
element 8. We say that the function is not
defined for the value, 8. A function that is
not defined for some argument values is called
partial. 

If we wanted to be mathematically precise in 
stating that there is no integer square root 
of 8, we could write ¬ ∃ n: ℕ | n * n = 8.
A mathematician would say this as "there does 
not (¬) exist (∃) a natural number (ℕ), n,
such that n * n = 8." We can make this semi-
formal statement formally precise in Lean,
as what we call a proposition. A proposition
is a claim that some statement is true. Here
the statement is that ¬∃ n: nat, n * n = 8.
-/

lemma no_sqrt8: ¬ ∃ n: nat, n * n = 8 := sorry

/-
To formalize (make mathematically precise) a 
proposition in lean, we define an identifier
(here no_squrt8) whose value is ultimately 
meant to be a proof of the proposition. We 
next state the proposition itself. Finally,
we give a proof of the proposition (if there
is one, of course). In this case, we use the
Lean construct, sorry, to "apologise" for 
not (yet) knowing how to give such a proof. 
Sorry tells Lean to take our word for it
and accepts the proposition as being true,
whether it really is or not! Using sorry to
get Lean to accept a false proposition as
true is obviously not a good idea. It makes
a contradiction from which anything can then
be proved true, making the logic useless.
-/

/-
An even better way to explain that there is
no natural number square root of 8 would be
to claim that there is no natural number, s,
such that the pair, (8, n), is in f. (Again
we skip out on trying to provide a proof at
this point. We'll get to that later.)
-/

lemma no_sqrt8': ¬ ∃ s, (8, s) ∈ f := sorry

/-
You can pronounce this like so: there does 
not exist an (or, there is no) s such that 
the pair (8, s) is in f; please accept this
claim as true even though we don't give an
actual proof.
-/

/-
EXERCISES: 

Write a similar lemma without giving a proof 
stipulating that there is no square root of 
10 in the natural numbers.
-/

/-
This is a great way to specify our function, f.
The problem is that you can't compute with such
a definition. It is "declarative in the sense
that it declares what the function f, is, but it
is not procedural, in that it does not give us a
step-by-step procedure for computing a value of
f(x) given a value of x.

The best that we can do with such a declarative
specification is assert that certain facts are
true about it, which we would then be left to try
to prove to be correct. Such assertions are called
propositions.
-/

/-
For example, in pencil-and-paper math, one might
write the proposition, (3, 4) ∈ f_set. The ∈ is 
pronounced "is in", so the overall proposition 
would be pronounced, "the pair, (3, 4), is in f. 
Here's how we can write this proposition in Lean.
We explain the notation below.
-/

lemma three_four_is_in_f : (3, 4) ∈ f := sorry

/-
The "lemma" keyword indicates that we're about 
to define a proposition. We give the proposition
the name, three_four_is_in_f. The proposition is
that (3, 4) ∈ f. Finally we tell Lean that we are
sorry, we can't give a proof at the moment, so
Lean should just take our word for it. (Later on 
we'll talk much more about proofs.) 
-/

/-
In this case, although we haven't tried, it
really is possible to give a proof, which
would show beyond any reasonable doubt that
it really is true (3, 4) is in f.

Of course there are many propositions that are
perfectly fine as propositions but that are
not true, and therefore for which it should 
be (and is) impossible to give a proof. One
such proposition is that the pair, (3, 3), is
in f. 
-/

lemma three_three_is_in_f: (3, 3) ∈ f := _

/-
We don't use sorry here because we don't 
want Lean to accept as a given that (3, 3)
is a pair in f. It's not. 

Instead of sorry, we  use an underscore.
It's called a placeholder. Lean issues an
error saying that it can't figure out how
to fill in that placeholder with a valid
proof. That would of course require that
Lean Lean come up with a proof that doesn't 
exist; so it's not going to happen. The 
error message can be read as saying, "Hey, 
I can't figure out what proof goes here."
-/

/-
The proposition that (3, 3) is NOT in f_set
is true, of course . A mathematician would 
write either ¬ (3, 3) ∈ f or (3, 3) ∉ f.
These are two notations for the same idea.
(Just hover over these special symbols to
have Lean tell you what to type to use them
in your own Lean code.) Again, even though
in principle a proof could be given here, 
we skip it for now and apologise instead.
-/

lemma three_three_not_in_f: (3, 3) ∉ f := sorry

  
/-
EXERCISE: Use set comprehension notation to specify
the square root function.
-/

/-
    sqrt = { (x, y) | y * y = x }
-/

/-
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



-- REPRESENTING FUNCTIONS AS FUNCTIONAL PROGRAMS

/-
Whereas a mathematician generally thinks of a 
function as a set of pairs, with one pair for each 
argument value for which the function is defined, 
a programmer, on the other hand, thinks of a 
function as a kind of machine that takes the first 
element of such a pair as an argument, and that 
computes and returns the corresponding second
element. For example, if implement the function 
f(x) = x + 1 as a program, let's also call it 
f_prog, then we could write and evaluate the
expression f_prog(3) and the machine would 
compute and return the value 4. 
-/

/- Rather than defining a function as a set of
pairs, a "functional program" says, "if you give 
me a value for x, I will compute and return the 
corresponding value of f(x). The program thus 
*implicitly* represents the set of pairs of the 
function being represented. 

So let's turn from declarative representations
of functions to computational representations.

In particular, we now see how we can write a
function is a mathematically clear way that
nevertheless supports computation of results
given arguments. The trick is to represent a
function not in a procedural language, such 
as Python, but in a pure functional language.

There are many such languages. Indeed, even
popular, industrial-strength procedural
languages, such as Java and Python, are 
increasingly supporting programming in a
functional style. But nothing beats a real 
pure functional language for clarity and
precision.

You'll recall that one way a mathemtician
would write our function is as f(x) = x + 1.
Now look at how we'd "implement" f in the
pure functional programming language of Lean.
-/


def f_prog (x: ℕ) := x + 1

/-
We define f_prog to be a function taking
an argument, x, of type ℕ, and returning
(or reducing to) the value of that x plus
1. 
-/

/-
We can now use the #reduce command in
Lean to reduce expressions in which this
function is applied to an argument to
compute the corresponding result.
-/

#reduce f_prog 3

/-
If we check the type of f_prog, we find
that Lean says it's of type ℕ → ℕ. 
-/

#check f_prog

/-
This can be read as "natural number to 
natural number." That is, f_prog takes a
natural number and reduces it to another
natural number. The observant reader will
understand that what this is really saying
is that "f_prog is a value of type ℕ → ℕ."
The value of f_prog is one of many possible
functions taking nats to nats.
-/

/-
EXERCISE: Define g_prog to be a function
from ℕ → ℕ that reduces any given argument
x: ℕ to the value, x * x. Check its type
to confirm that this function is also of
type ℕ → ℕ. You have thus now defined two
values, each functions, both of this type.
Yes, functions are values, too, in a pure
functional programming language, Later on
we'll see that we can do compute with 
values of function types  just as we can 
compute with values of numerical types.
Mathematicians view functions as values.
Our good luck is that we can now use pure
functional languages to automate computing
with functions values.
-/

/-
Before we continue, we provide alternative
notations for defining f_prog.

The first declares f_prog' (we add a prime
to the name to make it unique) as a value of
type, ℕ → ℕ, and then uses what we call 
lambda notation to represent the function
"value" assigned to f_prog'.
-/

def f_prog': nat → nat := 
    λ x, x + 1

/-
The first line declares that f_prog' will
be bound to a value of type ℕ → ℕ. The
second line defines the value so bound.
The notation uses the Greek letter lambda,
which you can just pronounce from now on
as "a function that takes an argument, ...".
The argument it takes is called x. The
body of the function is the expression,
x + 1. The whole "lambda expression" can
thus be read as "a function that takes an
argument, x (already declared to be of type
ℕ by the way)" and that returns the value,
x + 1 (which we've also told Lean should
be of type ℕ.)
-/

/-
Without giving a formal proof, we claim
truthfully here that f_prog' is exactly
the same function as f_prog.

EXERCISE: (1) Use #check to confirm that
the types of f_prog and f_prog' are the 
same. Then use #reduce to test the claim
that f_prog and f_prog' reduce to the same
results when applied to the same arguments.
-/

/-
Finally, we note we've left out explicit
type declarations in a few places where 
Lean can infer them automatically. Here
we present versions of f_prog and f_prog'
that include explicit type declarations.
Sometimes it's helpful to people to give
explicit declarations. Oftentimes it's
better to leave them out, to make the
code easier to read.
-/

def f_prog'' (x: nat): nat := x + 1

/-
Here we declare the result type. Lean
could have figured it out by "seeing"
that the argument is a ℕ, and knowing
that a ℕ plus 1 is also a ℕ. 
-/

/-
In the following code we tell Lean that 
both the argument and result are of type 
ℕ, even though  it already knows that is
the case from the ℕ → ℕ type declaration.
-/

def f_prog''': nat → nat := 
    λ x: nat, (x + 1: nat) 

/-
Leave out explicit type declarations 
when (1) Lean can infer them, and (2)
the result code is more rather than
less clear. We think the original
definition of f_prog is pretty clear!
-/

-- EVALUATING (REDUCING) FUNCTION APPLICATION EXPRESSIONS

/-
In a pure functional language, a program is simply the 
expression of a ... wait for it ... mathematical function. 
A  function definition in such a language has an argument, 
or "formal parameter", (such as x), and an expression,
the "body" of the function, in which the formal parameter, 
x, can appear, as it does in the expression, x + 1. 

When such a function is applied to a value, such as 3, the
resulting expression is *evaluated* by substituting the actual
value (here 3) for every occurrence of the formal parameter 
(here x) in the function body (here x + 1). The resulting 
expression  (here 3 + 1) is itself then evaluated. Finally 
the resulting value is returned. That value is the result 
of "reducing" the original function application expression. 
-/

/-
Note that the argument to a function can be any expression that
itself reduces to a value of the right type. Here's an example.
-/

#reduce f_prog (2 + 2)

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

#reduce f_prog (f_prog (f_prog 4))

/-
EXERCISES: more to come.
-/


