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
well, using set comprehension notation, as follows:
-/


def f := { p: ℕ × ℕ | p.2 = p.1 + 1 }

/-
This can be read as saying, "We define f to
be the set of values, p, where each p is a 
pair of natural numbers, where the second 
component of p is equal to the first plus 
one.
-/

/-
We now take a few paragraphs to drill down
on some details.
-/

/-
First, some new information about Lean.
The #check command in Lean will tell us the
type of an object. Checking the type of f
reveals that it is indeed a set of pairs of
natural numbers. Hover your mouse pointer
over the #check command. The message you
get back says that the type of f is what
you can read as "set of pairs of natural 
numbers."
-/

#check f

/-
We can denote specifici pairs of natural 
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
between arguments and results without
having to say anything about how to
compute results given arguments. Here
for example is a specification of the
square root function for natural 
numbers.
-/

def sqrt_nat := { p: ℕ × ℕ | p.2 * p.2 = p.1 }

/-
The pairs, (9, 3), (4, 2), and (1,1 ) are in 
this function, but (9, 4) isn't because it is
not the case that 9 = 4 * 4.
-/

/-
This specification is very clear. Consider,
by contrast, a Python program to compute 
natural roots of natural numbers: it would 
not be anywhere near as expressive. It might
for example use a loop to check each number,
n, between zero and an argument, a, to see 
if n * n is equal to a, returning n if it
satisfies this condition or an error if it
can't find such an n.
-/

/-
A second advantage of this declarative style
of specification is that it let's us specify
partial functions without having to explain
anything about values on which a function is
undefined.

Consider the argument 8, for example. There is
no natural number, n, such that n * n = 8. So
there is no pair in this function with first 
element 8. We say that the function is not
defined for the value, 8. A function that is
not defined for some argument values is called
partial. If we wanted to be really precise,
we could write ¬ ∃ n: ℕ | n * n = 8, which a
mathematician would pronounce as "there does 
not (¬) exist (∃) a natural number (ℕ), n,
such that n * n = 8." We can make this semi-
formal statement formally precising in Lean.
-/

lemma no_sqrt8: ¬ ∃ n: nat, n * n = 8 := sorry

/-
We first name then state the proposition,
and we finally apologise for not (yet) being
able to give Lean an actual proof of this
claim, while telling Lean to just take our
word for it, at least for now.
-/

/-
An even better way to explain that there is
no natural number square root of 8 would be
to claim that there is no natural number, s,
such that the pair, (8, n), is in f.
-/

lemma no_sqrt8': ¬ ∃ s, (8, s) ∈ f := sorry

/-
You can pronounce this like so: there is no s
such that the pair (8, s) is in f. 
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
is a pair in f. It's not. Forcing Lean to
accept that (3, 3) is in the function would
make the set of facts that Lean is working
with inconsistent, and an inconsistent set
of facts is basically useless, as anything
then becomes provable. 0 = 1. true = false.
Etc.

Instead of sorry, we just use an underscore.
It's called a placeholder. Lean issues an
error saying that it can't figure out how
to fill in that placeholder, which in this
case would require that Lean come up with 
a proof that doesn't exist. The erros just
says, "Hey, I can't figure out what proof
goes here."
-/

/-
The proposition that (3, 3) is NOT in f_set
is true, of course . A mathematician would 
write either ¬ (3, 3) ∈ f or (3, 3) ∉ f.
(Just hover over these special symbols to
have Lean tell you what to type to use them
in your own Lean code.) Again, even though
in principle a proof could be given here, 
we skip it for now and apologise instead.
-/

lemma three_three_not_in_f: (3, 3) ∉ f := sorry


-- REPRESENTING FUNCTIONS AS PURE FUNCTIONAL PROGRAMS


def f_prog (x: nat): nat := x + 1


#reduce f_prog 3

def f_prog': nat → nat := λ x, x + 1

#reduce f_prog' 3



  
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


