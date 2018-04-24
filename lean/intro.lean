/-
At this point, we've proposed and validated
(using truth tables) a set of fundamental
inference rules. Unfortunately, using truth
tables doesn't scale well. We thus play an
important game, now, where we simply accept
the inference rules as valid transformation
between sets of premises and conclusions. We
view the Ps, Qs, Rs in the rules we validated
as "standing for" arbitrary propositions, and
we now apply the rules without having to go
back and validate the results "semantically"
(using truth tables). We thus transition 
from what we call "semantic entailment" to
"syntactic entailment," which finally moves
us into the realm of symbolic logic and proof.

We now also shift tools, from Dafny, which
allows us to write logic, but which largely
hides the proofs and their construction, to
Lean, which is what we call a proof assistant.
Many propositions are too difficult for tools
such as Dafny to prove automatically. If we
still want the assurances of correctness (of
software or even just of pure mathematics)
provided by a strongly typed checker, then
we have to use a tool in which we manipulate
both propositions and proofs explicitly. We
are now there. 

The purpose of this initial unit is to give
you an introduction to the fundamental concepts
of propositions and proofs when using a proof
assistant tool, here the Lean Prover. The key
point of this chapter is that different forms
of propositions require the use of different
proof strategies and have different forms of
proofs. These are ideas that are fundmental
to discrete mathematical whether or not you
are using a proof assistant tool such as 
Lean. The benefits of using Lean include
nearly absolute assurance that you haven't
made mistakes: that proofs don't contain
errors. This technology is now also at the
forefront of important research not only in 
ultra high assurance software and systems, 
but even in pure mathematics. Wecome to the
cutting edge!
-/

/- **** PROPOSITIONS AS TYPES **** -/

/-
Here's a typical definition, in this case,
of a variable, x, bound to the value, 1, of
type, nat.  
-/
def x: nat := 1

/-
In Lean, you can check the type of a term
by using the #check command. Hover your
mouse over the #check in VSCode to see 
the result.
-/

#check 1
#check x

/-
Lean tells you that the type of x is nat.
It uses the standard mathematical script N
(ℕ) for nat. You can use it too by typing 
"\nat" rather than just "nat" for the type.
-/

def x': ℕ := 1

/-
You can evaluate an expression in Lean using
the #eval command. (There are other ways to
do this, as well, which we'll see later.) You
hover your mouse over the command to see the
result.
-/

#eval x

/-
In Lean, definitions start with the keyword, 
def, followed by the name of a variable, here
x; a colon; then the declared type of the
variable, here nat; then :=; and finally an
expression of the right type, here simply 
the literal expression, 1, of type ℕ. Lean
type-checks the assignment and gives and error
if the term on the right doesn't have the same
type declared or inferror for the variable on 
the left.
-/


/- ****** TYPES ARE VALUES, TOO ****** -/

/-
In Lean, every term has a type. A type is a
term, too, so it, too, has a type. We've seen
that the type of x is nat. What is the type
of nat? 
-/

#check nat

/-
What is the type of Type?
-/

#check Type

/-
What is the type of Type 1?
-/

#check Type 1

/-
You can guess where it goes from here!
-/


/- ****** PROPOSITIONS ****** -/

/-
Lean and similar constructive logic proof
assistants unify and automate mathematical
logic and computing. So propositions are
now values, and so are proofs. As such, 
propositions must have types. Let's write 
a few simple propositions and check to see
what their types are.
-/

-- zero equals zero; this is a proposition
#check 0=0

-- every natural numbers is non-negative
#check ∀ n: nat, n >= 0

-- Get the forall symbol by typing "\forall"

-- every natural number has a successor
#check ∀ n: ℕ, ∃ m: ℕ, m = n + 1

-- Get the exists symbol by typing "\exists"

-- Propositions are values, too!

def aProp := ∀ n: ℕ, ∃ m: ℕ, m = n + 1

#check aProp

/-
In each case, we see that the type of a 
proposition is Prop. What's the type of Prop?
-/

#check Prop

/- 
Ok, the type of Prop is also Type. So what
we have here is a type hierarchy in which the 
familiar types, such as nat, have the type, 
Type, but where there's also a type, called 
Prop, that is also of type, Type, and that, 
in turn, is the type of all propositions.

So let's start again with x := 1. The value
of x is 1. The type of the value, 1, is nat.
The type of nat is Type. From there the type
of each type is just the next bigger "Type n.""  

We've also seen that a proposition, such as
0=0, is of type, Prop, which in turn has the
type, Type. But what about proofs?
-/


/- ** PROOFS: PROPOSITIONS ARE TYPES! ** -/

/-
So what about proofs? They crazy idea that
Lean and similar systems are built on is that
propositions can themselves be viewed as types,
and proofs as values of these types! In this
analogy, a proof is a value of a type, namely
of the proposition that it proves, viewed as
a type. So just as 1 is a value of type nat,
and nat in turn is a value of type, Type, so
a proof of 0=0 is a value of type 0=0! The
proposition is the type, the proof, if there
is one, is a value of such a type. The type
of a proposition (itself a type) is Prop.
And the type of Prop is Type. To see this
clearly, we need to build some proof values.
-/

/-
Here (following this comment) is another 
definition, of the variable, zeqz. But 
whereas before we defined x to be of the
type, nat, now we define zeqz to be of the
type, 0=0. We're using a proposition as a
type! To this variable we then assign a 
value, which we will understand to be a
proof. Proof values are built by what we
can view as inference rules. The inference
rule, rfl, build a proof that anything is
equal to itself 
-/
def zeqz: 0 = 0 := rfl

/-
The proof is produced the rfl inference rule.
The rfl "proof constructor" (that is what an
inference rule is, after all) is polymorphic, 
uses type inference, takes a single argument,
a, and yields a proof of a = a. The value in
this case is 0 and the type is nat. What the
rule rule says more formally is that, without 
any premises you can conclude that for any 
type, A, and for any value, a, of that type, 
there is a proof of a = a. For example, if you 
need a proof of 0=0, you use this rule to build
it. The rule infers the type to be nat and the 
value, a, to be 0. The result is a proof of 
the proposition 0 = 0. The value of zeqz is 
thus a *proof*, a proof of its type, i.e., 
of the logical proposition, 0 = 0. Checke the
type of zeqz. Its type is the proposition that
it is a proof of!
-/
#check zeqz

/-
It helps to draw a picture. Draw a picture
that includes "nodes" for all of the values
we've used or defined so far, with arrows
depicting the "hasType" relation. There are
nodes for 1, x, zeqz, nat, Prop, Type, Type 1,
Type 2, etc. 
-/

/-
When we're building values that are proofs
of propositions, we generally use the keyword,
"theorem", instead of "def". They mean exactly
the same thing to Lean, but they communicate 
different intentions to human readers. We add
a tick mark to the name of the theorem here
only to avoid giving multiple definitions of
the same name, which is an error in Lean.
-/
theorem zeqz': 0 = 0 := rfl

/-
We could have defined x := 1 as a theorem.
-/

theorem x'': nat := 1

/-
While this means exactly the same thing as
our original definition of x, it gives us an
entirely new view: a value is a proof of its
type. 1 is thus a proof of the type nat. Our
ability to provide any value for a type gives
us a proof of that type. The type checker in
Lean of course ensures that we never assign
a value to a variable that is not of its
declared or inferred type.
-/

/- ********** TRUTH ********** -/

/-
What does it mean for a proposition to be true
in Lean? It means exactly that there is a proof,
which is to say that it means that there is some
value of that type. A proposition that is false
is a good proposition, and a good type, but it
is a type that has no proofs, no values! It is 
an "empty," or "uninhabited" type. The type, 1=0,  
has no values (no proofs). There is no way to
produce a value of tihs type. 
-/


/- ********** NEXT STEPS ************ -/

/-
With this background in hand, we can now use
what we've learned to start to investigate the
world of mathematical logic and proof at a very
high level of sophistication and automation! 

In particular, we now start to explore different
*forms of propositions* and corresponding *proof
strategies*. The rest of this unit focuses on
propositions that claim that two terms are equal,
and the proof strategy we see is called "proof
by simplification and by the reflexive property
of equality".
-/

/- ******** PROOFS OF EQUALITY ******* -/

/-
An expression, v1=v2, is a proposition that
asserts the equality of the terms v1 and v2.
The terms are considered equal if and only 
if one can produce a proof of v1=v2. There
is an inference rule defined in Lean that
can produce such a proof whenever v1 and v2
are exactly the same terms, such as in 0=0. 
This rule can also produce a proof whenever
v1 and v2 reduce (evaluate) to identical 
terms. So we can also produce a proof of 
0+0=0, for example, because 0+0 reduces
to 0, and then you have identical terms on
each side of the =. This notion of equality 
is called "definitional equality"). As you'd
expect, it's a binary, reflexive, symmetric,
and transitive relation on terms. It is also
polymorphic, and so can be used for any two
terms of the same type, A, no matter what A
is. The Lean inference rule that produces 
proofs of definitional equality is just rfl.

Here (following) are several terms that are 
definitionally  equal even though they're not 
identical. rfl is happy to build proofs for 
them. The second example illustrates that
terms that look pretty different can still 
be definitionally equal. On the left we have
a nat/string pair. The .1 after the pair is
the operator that extracts the first element
of the pair, here term 1-1. This term then 
reduces to 0. The terms on either side of 
the = reduce to the same term, 0, which 
allows rfl to complete its work and return
a value that is accepted as being of the
right type, i.e., as a proof of equality. 
-/
theorem t0 : 1 - 1 = 5 - 5 := rfl
theorem t1 : (1-1, "fidgblof").1 = 0 := rfl

/-
What you are seeing here is a strategy of
proving propositions that assert equalities 
in two steps: first simplify (evaluate) the 
expressions on either side of the =, and 
then certify a proof of equality if and 
only if the resulting terms are identical. 
Whether you are using a proof assistant tool
such as Lean or just doing paper-and-pencil
mathematics, this is a fundamental strategy
for proving propositions of a certain kind,
namely propositions that assert equalities.
-/



/- ND INTRODUCTION AND ELIMINATION RULES -/

/- ******* True Introduction ******** -/

/-
Recall from our introduction to inference 
rules in propositional logic that the
proposition, pTrue, is true without any
preconditions. We wrote the rule like this:
([],pTrue), and we called it "true intro".
We proved the rule semantically valid, so
we can write  [] |= pTrue. That is, from
an empty context (no previous assumptions)
we can conclude that pTrue is true. 

In lean, "true" is the true proposition.
You can check that "true" is a proposition
using #check.
-/

#check true

/-
Note: the proposition, true, is different
than the Boolean value, true. The Boolean
value, true, written "tt" in Lean, is one
of the two values of the bool datatype. It
is not a proposition.  Chek it out.
-/

#check tt


/-

In Lean and similar proof assistants, 
propositions, such as true in Lean, can
be defined inductively. The keyword for
an inductive datatype in Dafny is just
"datatype". Recall the definition of 
our syntax for propositional logic, 
for example. The values of a type are
defined by a list of contructors. 

As proofs are values of types, we can
define propositions as types and proofs
of such propositions as values produced
by constructors. The simplest example 
is the proposition, true, in Lean. It's
defined in Lean's core library like so:

inductive true : Prop
| intro : true

This says that true is of type Prop,
i.e., is a proposition, and it has just
one value, proof, namely "intro". The
constructor says, "intro" is of type
(i.e., is a proof of) true. The intro
constructor takes no arguments and so
is always available as a proof of true.
We thus have our true introduction: just
use the constructor. Here we should how
to assert that the proposition "true" is
true (there's a proof for it) by giving
the one and only proof, namely "intro".
To refer to a constructor of a type,
use the type name dot constructor name.
-/

theorem proofOfTrue: true := true.intro

/-
This isn't a very useful rule of natural
deduction, as it doesn't really tell you
anything you didn't already know. It is not
commonly used in proofs.
-/



/- *** The proposition, false  *** -/


/-
In Lean, false is also a proposition. By
contrast, the Boolean false value in Lean
is written as ff.
-/

#check false

/-
false is meant to be the proposition 
that is never true, i.e., that can never
be proved, i.e., for which there is no 
proof. As a type, it has no values. It
is an uninhabited type. 

The false proposition/type is defined 
inductively as having type, Prop, and
as having exactly no constructors! It's 
a proposition but there is no way to 
contruct a proof. Here's the definition
of false from the Lean core libraries:

inductive false : Prop

That's it. Look, no constructors!

There is no false introduction rule.
There is no way to introduce a proof of
false. There is no proof of false. We'll
discuss false elimination later in this
chapter.
-/

/- ***** PROOFS OF CONJUNCTIONS ****** -/

/- 
Key Point: Propositions of different kinds
require the use of different proof strategies.
Learning to recognize what kind of proposition
you're looking at, and then to pick the right
proof strategy, is critical. To illustate this
point, we now look at how to produce proofs 
of conjunctions: propositions of the form,
P ∧ Q. The key idea is simple: a proof of 
P ∧ Q can be constructed if and only if you
have (or can produce) both a proof of P and 
a proof of Q. In that case, you can use the
and introduction rule to build the desired
proof. Remember the rule: [P, Q] ⊢ P ∧ Q.
Now we can write this rule to distinguish
propositions, such a P and Q, from proofs.
[pfP: P, pfQ: Q] ⊢ (pfP, pfQ): P ∧ Q. In
other words, if I have a proof, pfP, of P 
(a value, pfP, type, P!), and a proof, pfQ,
of Q, then I can build a proof, (pfP, pfQ),
of P ∧ Q; and the proof of the conjuction is
just the ordered pair of the individual proof
values! The and introduction rule can be
understood as a function that takes two
proof values and returns them as an ordered
pair, which in Lean proves the conjunction 
of the corresponding propositions. 

Whether using a proof assistant  or just 
doing paper and pencil math, the strategy
for proving a conjunction of propositions
is to split the conjunction into its two
component propositions, obtain proofs of
them individually, and then combine/take 
the two proofs as a proof of the overall
conjunction. The benefit of using a proof
assistant is that aspects are automated,
and you're not allowed to make mistakes. 
-/

/-
So that we can play around with this idea,
given that we already have a proof of 0=0
(zeqz), we now contruct a proof of 1=1 so 
that we have two propositions and proofs 
to play with. 
-/
theorem oeqo : 1 = 1 := rfl

/--------- And Introduction -----------/

/-
To start, we conjecture that 0=0 /\ 1=1. We 
already have a proof of 0=0, namely zeqz.
And we already have a proof of 1=1, namely
oeqo. So we should be able to produce a
proof of 0=0 /\ 1=1 by using the "and
introduction" inference rule. Remember
that it says that if a proposition, P, is
true (and now by that we mean that we
have a proof of it), and if Q is true,
then we can deduce (construct a proof!)
that P ∧ Q is true. Here's how you do
that in Lean. (Note: we get the logical 
and symbol, ∧, by typing "\and", i.e.,
backslash-and, followed by a space.)
-/
theorem t2: 0=0 ∧ 1=1 :=  -- proposition
    and.intro zeqz oeqo   -- build proof

/-
NOTE!!! Whereas we typically define
functions to take a single tuples of 
argument values, and thus write the
arguments to functions as tuples (in 
parenthesis), e.g., inc(0), we write 
the arguments to proof constructors 
(inference rules) without parenthesis
and without commas between values. So 
here for example, and below, we write 
"and.intro zeqz oeqo" rather than 
and.intro(zeqz, oeqo). Be careful when
you get to the exercises to remember
this point. 
-/

/-
The preceding code should make it pretty
clear that and.intro is, for all intents
and purposes, a function that takes proofs
of 0=0 and 1=1, respectively, and constructs 
a proof of 0=0 /\ 1=1. As we've already 
discussed, such a proof is in essence the
ordered pair of the given proof values.
As such, we should be able to extract the
individual proofs from such a pair, and
that is what the and elimination rules do!
There are two, one to obtain each element.
Thus from a proof of P ∧ Q we can apply
the and elimination rules to obtain a
proof of P and a proof of Q.
-/

/--------- And Elimination -----------/

/-
And introduction creates a proof of a 
conjunction from proofs of its parts (its
"conjuncts"). Such a proof is a pair the
elements of which are the two "smaller" 
proofs. Given such a proof/pair, the and
*elimination* rules return one of the 
other the component proofs. For example,
from a proof of P ∧ Q, and.elim_left will
return the contained proof of P, and the
and.elim_right rule returns the proof of 
Q.
-/

theorem e1: 0=0 := and.elim_left t2

/-
This says that a value, e1, of type 0=0, 
i.e., a proof of 0=0, can be obtained by
applying and.elim_left to t2, which is a
proof of 0=0 ∧ 1=1, which is to say that
it is a pair of proofs, one of 0=0 and 
one of 1=1. The and elimination rules
are just "project operators" on pairs of
proofs.
-/




/-
Natural deduction, which is the proof 
system that we're using here, is a set 
of functions (inference rules) for taking 
apart (elimination) and putting together 
(introduction) proofs of propositions to
produce proofs of other propositions. 

This natural deduction proof systems was
invented long before autoamted tools, and
is one of the fundamental systems for 
precise logical reasoning. The Lean Prover
and similar "proof assistants" automate
and use strong, static type checking to 
make sure that you can never produce an 
incorrect proof, because you're never
allowed to pass arguments of the wrong
types to the inference rules, and at the
end of the day, you don't have a proof
of a complex proposition unless the type
checkers accepts it as a value of the 
type (proposition) it is inteded to prove.

Take-away: You're learning the natural 
deduction style of producing proofs of
mathematical conjectures; but unlike the
students doing this with paper and pencil
and no tool to help, you have the benefit
of automation and a highly trustworthy
correctness checker. The cost is that
now you can't be slooppy. Inded, you
have to be very precise about every 
step. Experienced mathematicians like
to skip many steps in writing proofs,
when they (think they) know that the
details will all work out. The upside
is that it's easier to "write the code."
The downside is that errors can easily
go undetected. Many errors in proofs of
important theorems have only been found
years after the proofs were reviewed by
mathematicians and accepted as true in
the community. When lives depend on the
correctness of proofs, it can be worth
the trouble to make sure they're right.
-/


/-******** FUNCTIONS **********-/

/-
Next we turn to proofs of propositions in
the form of implications, such as P → Q.
Up until now, we've read this implication
as a proposition that claims that "if P is 
true then Q must be true." 

But now we've understood "truth" to mean
that there is a proof. So we would view
the proposition, P → Q, to be true if 
there's a proof of P → Q. And we have
also seen that we can view propositions
as types, and proofs as values. So what
we need to conclude that P → Q is true 
is a proof, i.e., a value of type P → Q. 

What does such a value look like? Well,
what does the type P → Q look like?! We
have seen such types before. It looks 
like a function type: for a function
that when given any value of type, P,
returns a value of type, Q. And indeed,
that's just what we want! We will view
P → Q, the proposition, to be true, if
and only if we can produce a *function*
that, when given any proof of P, gives
us back a proof of Q. If there is such
a function, it means that if P is true 
(if you can produce a proof value for
P) then Q is true (you can obtain a
proof for Q) just by calling the given
function. 

To make this idea clear, it will help
to spend a little more time talking 
about functions and function types. In
particular, we'll introduce here a new
notation for saying something that you
already know how to say well: a way to
represent function bodies without having
to give them names. These are given the
somewhat arcane name, lambda expressions,
also written as λ expressions. So let's
get started. 
-/

/-
We can define functions in Lean almost
as in Dafny. Here are two functions to
play with: increment and square. Go back
and look at the function.dfy file to see
just how similar the syntax is.
-/
def inc(n: nat): nat := n + 1
def sqr(n: nat): nat := n * n
def comp(n: nat): nat := sqr (inc n)

/-
Now's a good time to make a point that 
should make sense: functions are values
of function types. Our familiar notation
doesn't make function types explicit, but
it shouldn't be a stretch for you to 
accept that the type of inc is nat → nat.
Lean provides nice mathematical notation
so if you type "\nat" you'll get ℕ. So,
that type of inc is best written, ℕ → ℕ. 

We could thus have declared inc to be a
value of type ℕ → ℕ, to which we would 
then assign a function value. That is a
new concept: we need to write formally
what we'd say informally as "the function
that takes a nat, n, as an argument and
that returns the nat, n + 1 as a result."

The way we write that in Lean (and in 
what we call the lambda calculus more
generally) is "λ n, n + 1". The greek
letter, lambda (λ), says "the following
variable is an argument to a function".
Then comes a comma followed by the body
of the function, usually using the name
of the argument. Here then is the way
we'd rewrite inc using this new notation.
-/
def inc': ℕ → ℕ := λ n: nat, n + 1

/-
As you might suspect, from the function
value, Lean can infer its type, so you
don't have to write it explicitly. But
you do have to write the type of n here,
as Lean can't figure out if you mean nat
or int or some other type that supports
a * operator.
-/
def sqr' := λ n: nat, n * n

/-
Given a function defined in this way, 
you can apply it just as you would
apply any other function.
-/
def sq3 := sqr' 3 

/-
Don't believe that sq3 is therefore of
type nat? You can check the type of any
term in Lean using its #check command. 
Just hover your mouse over the #check.
-/
#check sq3

/-
Do you want to evaluate the expression
(aka, term) sq3 to see that it evaluates
to 9? Hover your mouse over the #eval.
-/
#eval sq3

/-
To give a proof (value) for a proposition
in the form of an implication, we'll need 
to provide a function value, as discussed.
While we could write a named function using 
def and then give that name as a proof, it 
is often easier to give a lambda expression
directly, as we'll see shortly.
-/

/-
We can also define recursive functions,
such as factorial and fibonacci using
Lean's version of Dafny's "match/case" 
construct (aka, "pattern matching"). 

Here's how you write it. The first line
declares the function name and type. The
following lines, each starting with a bar
character, define the cases. The first
rule matches the case where the argument
to fac is 0, and in that case the result
is 1. The second case, which is written
here a little differently than before,
matches any value that is one more than
some smaller argument, n, and returns 
that "one more than n" times the factorial
of the samller number, n. Writing it this
way allows Lean to prove to itself that the
recursion terminates.  
-/
def fac: ℕ → ℕ 
| 0 := 1
| (n + 1) := (n + 1) * fac n

/-
We can now write some test cases for our
function ... as little theorems! And we 
can check that they work by ... proving
them! Here once again our proof is by the
reflexive property of equality, and lean
is automatically reducing (simplifying) 
the terms (fac 5) and 120 before checking
that the results are the same. fac 5 does
in fact reduce to 120, so the terms, fac 5,
and 120, are definitionally equal, and
in this case, rfl constructs a proof of
the equality.
-/
theorem fac5is120 : fac 5 = 120 := rfl

/- ******* PROOFS OF IMPLICATIONS ******* -/
/-
So far we've see how to build proofs of
equality propositions (using simplification
and reflexivity, i.e., rfl), of conjunctions
(using and.intro), and of disjuctions (using
one of the or introduction rules). What about
implications? 
-/

/- Arrow Introduction -/ 

/-
Suppose we wanted to show, for example, that 
(1=1 ∧ 0=0() → (0=0 ∧ 1=1). Here the order of
the conjuncts is reversed.

How to think about this? First, remember that
an implication, such as P → Q, doesn't claim 
that the conclusion, P, is necessarily true.
Rather, it only claims that *if the premise 
is true, then the conclusion is true. Now, by 
"true", we mean that we have or can construct
a proof. An implication is thus read as saying 
if you assume that the premise, P, is true, in
other words if you assume you have a proof of
P, then you can then derive a proof of the 
conclusion, Q. 

But proofs are just values of (these strange 
propositional) types, and so a proposition in 
the form of an implication, such as P → Q is 
true when we have a way to convert any value 
(proof) of type P into a value (proof) of type 
Q. We call such a thing a function! 

Think about this: the implication, P → Q is 
true if we can define a function (body) of 
this type, P → Q. Here's the actual code from
the Lean core library:  

def implies (a b : Prop) := a → b

So now, think about how to write a function
that takes an argument of type 1=1 ∧ 0=0 and
that returns a result of type 0=0 ∧ 1=1. To
make it even clearer, understand that a proof
of a conjunction is a pair of proofs, the and
elimination rules just give you the values in
such pairs, and the and introduction rule just
forms such an ordered pair given arguments of
the right types. The strategy for writing the
function we need is thus:

start with (proof of 1=1, proof of 0=0) as
a pair proving 1=1 ∧ 0=0; extract each of 
the component proofs, then construct and
return a pair constituting a proof of the
conjunction with the component proofs in 
the opposite order.
-/ 
/-
Here's an ordinary function that does the trick.
-/
def and_swap(premise: 1=1 ∧ 0=0): 0=0 ∧ 1=1 :=
    and.intro 
        (and.elim_right premise) 
        (and.elim_left premise)

/-
Now we can use it as a proof of the theorem.
-/
theorem and_commutes': 1=1 ∧ 0=0 → 0=0 ∧ 1=1 :=
    and_swap   -- just give function as proof


/-
Here's the same thing using a lambda. You can
see here how lambda expressions (also know as
anonymous functions) can make for cleaner code.
They're also essential when you want to return
a function.
-/
theorem and_commutes: 1=1 ∧ 0=0 → 0=0 ∧ 1=1 :=
  /- 
  a function taking premise, a proof of 
  1=1 ∧ 0=0, as an argument, and returning ...
  -/
  λ premise: 1=1 ∧ 0=0,  
  /-
  a proof of the conjunction reversed
  -/
    and.intro 
        (and.elim_right premise) 
        (and.elim_left premise)
  
/-
The bottom line here is that we introduce
an arrow by defining a function, which we
can also now pronounce as "by proving an
implication (which is done by giving such
a function)."
-/

/- Arrow Elimination-/

/-
Arrow elimination starts with an implication
(aka, function), in the context, along with 
a proof of its premise (i.e., an argument of 
the type that the function takes), and ends 
with a proof of the conclusion. This is just 
modus ponens! And just function application!
-/

theorem modus_ponens' (hImp: 1=1 ∧ 0=0 → 0=0 ∧ 1=1) 
                     (hc: 1=1 ∧ 0=0): 0=0 ∧ 1=1 :=
    (hImp hc)

theorem modus_ponens'': 
    (1=1 ∧ 0=0 → 0=0 ∧ 1=1) → 
        1=1 ∧ 0=0 → 
            0=0 ∧ 1=1 :=
    λ hImp, λ hc, (hImp hc)

/-
Arrow elimination is modus ponens is function
application to an argument. Here's the general
statement of modus ponens as a function that is
polymorphic in the types/propositions, P and Q.
You can see that the propositions are arguments
to the function, along with a P → Q function and
a (value) proof of (type) P, finally producing a 
(value) proof of (type) Q.
-/
theorem modus_ponens: ∀ P Q: Prop, (P → Q) → P → Q :=
    λ P Q: Prop, λ pfImp: P → Q, λ pfP: P, (pfImp pfP)

/-
We could of course have written that using 
ordinary function notation.
-/
theorem modus_ponens2 
    (P Q: Prop) (pfImp: (P → Q)) (pfP: P): Q :=
        (pfImp pfP)

/-
As an advanced concept, putting arguments in 
curly braces tells Lean to use type inference
to infer their values.
-/
theorem modus_ponens3
    {P Q: Prop} (pfImp: (P → Q)) (pfP: P): Q :=
        (pfImp pfP)

/-
Type inference can also be specified for lambdas
by enclosing parameters to be inferred in braces.
-/
theorem modus_ponens4: ∀ P Q: Prop, (P → Q) → P → Q :=
    λ P Q: Prop, λ pfImp: P → Q, λ pfP: P, (pfImp pfP)


/-
Compare the use of our modus_ponens function
with modus_ponens3. In the latter case, Lean
infers that the propositions (values of the
first two parameters) are P and Q, Such uses
of type inference improve code readaibility.
-/
section mp
variables P Q: Prop     -- assume in section
variable hImp: P → Q    -- assumption
variable hP: P          -- assumption    
#check modus_ponens P Q hImp hP
#check modus_ponens3 hImp hP
end mp


/- ***** PROOFS OF DISJUNCTIONS ***** -/

/-
To prove a conjunction, we saw that we 
need to construct a pair of proofs, one
for each conject. To prove a disjunction,
P ∨ Q, we just need a proof of P or a proof
of Q. We thus have two inference rules to
prove P ∨ Q, one takeing a proof of P and
returning a proof of P ∨ Q, and one taking
a proof of Q and returning a proof of P ∨ Q.
We thus have two or introduction rules in
the natural deduction proof system, one 
taking a proof of the left disjunct (P),
and one taking a proof of the right (Q).

For example, we can prove the proposition, 
0=0 ∨ 1=0 using an "or introduction" rule.
In general, you have to decide which rule
will work. In this case, we won't be able
to build a proof of 1=0 (it's not true!),
but we can build a proof of 0=0, so we'll
do that and then use the left introduction
rule to generate a proof of the overall
proposition. 

The or introduction rules in Lean are
called or.inl (left) and or.inr (right).
Here then we construct a proof just as
described above, but now checked by the
tool.
-/
theorem t3: 0=0 ∨ 1=0 := 
    or.inl zeqz

theorem t4: 1=0 ∨ 1=1 := 
    or.inr oeqo

/-
Once again, we emphasize that whether or
not you're using Lean or any other tool or
no tool at all, the strategy for proving a
disjunction is to prove at least one of its
disjucts, and then to take that as enough
to prove the overall disjunction. You see
that each form of proposition has its own
corresponding proof strategy (or at least
one; there might be several that work). In
the cases we've seen so far, you look at
the constructor that was used to build the
proposition and from that you select the
appropriate inference rule / strategy to
use to build the final proof. You then
either have, or construct, the proofs that
you need to apply that rule to construct
the required proof.

As a computational object, a proof of a
disjunction is like a discriminated union
in C or C++: an object containing one of
two values along with a label that tells
you what kind of value it contains. In
this case, the label is given by the
introduction rule used to construct the
proof object: either or.inl or or.inr.
-/

/- ******** FALSE ELIMINATION ******** -/

/-
There is no false introduction rule. If
there were, we'd be able to introduce a
proof of false, and that would be bad. It
would allow us to prove anything at all.

That this is the case is explained by the
false elimination rule. If given a proof
of false, we can use it to prove anything 
at all. Here we prove 0=1. That is, we'd 
be able to prove it if we started from a
contradiction. 

Here we see the use of false.elim in two
equivalent forms, differing only in the
movement of arguments from one side of the
colon to the other.
-/

theorem fe: false → 0 = 1 := 
    λ f: false, false.elim f

/-
The way to read the lambda expression is
as a function that if given a proof of
false applies false.elim to it to produce
a proof of 0=1. That proposition is an
implicit argument to false.elim, which
makes this notation less than completely
transparent; but that is what's going on.
Here's exactly the same "theorem" in the
form of an ordinary function definition.
-/

def fe' (f: false): 0=1 := false.elim f

/-
The good news, of course, is that while
these are perfectly good functions (and
implications), you can never use them,
because in a sound logic, you can never
produce a proof of false.

But suppose you could. Then you can use 
functions like these to produce proofs 
of anything at all. Here we use the fe 
function applied to a proof of false 
that we just assume exists to produce 
a proof of 0=1. You *do not* want to be 
able to prove false in a logic. If you 
can, the logic becomes useless, as one
then prove anything at all.
-/
section bad
variable f: false  -- assume proof of false
#check fe(f)       -- derive a proof of 0=1   
end bad            -- or anything else at all


/-
Here's a proof that shows that if you have a
proof of a proposition P and of its negation,
then that is tantamount to having a proof of
false, and so, again you can prove anything.
-/
theorem fromContraQ: ∀ P Q: Prop, P -> ¬ P -> Q :=
    λ P Q: Prop, 
        λ pfP: P, 
            λ pfNotP: ¬ P, 
                false.elim (pfNotP pfP) 

/-
We can't produce a contradiction in Lean except
by assuming one. We do so here within a section
to see this principle in action.
-/

section contra
variables P Q: Prop
variable pfP: P
variable pfNotP: ¬ P
-- the type of the next term is Q (proof of Q)
#check fromContraQ P Q pfP pfNotP
-- from a contradiction we can prove anything 
end contra


/- ******* NOT INTRODUCTION ********** -/

theorem notIntro: ∀ P Q: Prop, (P → Q) → ¬ Q → ¬ P :=
    λ (P Q: Prop) hImp QimpF, 
        λ pfP: P, (QimpF (hImp pfP))

def notIntro' {P Q: Prop} (hImp: P → Q) (QimpF: ¬ Q): ¬ P :=
    λ pfP: P, QimpF (hImp pfP)

/-
example (hpq : p → q) (hnq : ¬q) : ¬p :=
assume hp : p,
show false, from hnq (hpq hp)
-/

theorem fe'' : forall P: Prop, false -> P := 
    λ P: Prop, false.elim

/- ******* NEGATION INTRODUCTION ******* -/

/-
We are allowed to conclude ¬ P if we can show
that P leads to a contradiction: P → false. The
idea is a kind of proof by contradiction. If from
P we can prove "false" (which is supposed to be,
and is, impossible) then the assumption that P
is true must be wrong, and ¬ p must be true.

Indeed, Lean (and similar systems) define not P
as P -> false. Here's the actual code.

def not (a : Prop) := a → false

If we have a proof of ¬P (a function from P to
false) and (by some impossible means) a proof of
P, then we can derive a proof of false.
--/

/- Negation Introduction -/

/- 
A proof of (P → false) implies ¬P, because a
proof of (P → false) *is* a proof of ¬P. 
This is our negation introduction rule. 

-/
theorem f'': (1=0 -> false) -> ¬1=0 := 
    λ i: (1=0 -> false), i

/- Negation Elimination -/

/-
Negation elimination is just a special case of
arrow elimination. We eliminate an arrow (i.e. a
function) by applying it to an argument of the 
right
From a proof of ¬ P and a proof of P (i.e., from
a contradiction), we can derive a proof of false.
Of course if ¬ P is true, we'll never be able to
come up with a value of type P, so we can really
never use this function! 
-/
theorem f: ¬1=0 -> 1=0 -> false := 
  λ pf_n1e0: ¬1=0, λ pf_1e0: 1=0, pf_n1e0 pf_1e0

/-
There's a simpler way to write this, as a proof
of ¬ P simply is a proof of (P → false). So we
can prove the overall theorem by just returning
the assumed proof of ¬1=0. If you put parens 
around (1=0 → false) in the statement of the
theorem, the picture might be clearer. As, once
again, ¬ P simply means (P → false).
-/
theorem f': ¬1=0 -> 1=0 -> false := 
  λ pf_n1e0, pf_n1e0

/- ****** STRUCTURING COMPLEX PROOFS ******** -/

/-
The "sorry" keyword tells Lean to accept a theorem,
value, proof, by assumption, or "axiomatically." It's
a dangerous capability: it's easy to introduce a new
"fact" that contradicts one already known. But it is
very helpful in structuring larger proofs, in that you
can "stub out" parts of proofs, make overall proofs 
work, then go back and "backfill" by proving all of
the propositions you previously just "assumed away."
-/
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
sorry

/-
Using _ in place of sorry asks Lean to try to fill in a
proof for you. Hover the mouse over the "hole" and Lean
will tell you what inference needs to be validated *and*
the context available for validating it.
-/
theorem test' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
-- _
sorry

theorem test'' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
apply and.intro,
exact hp,
apply and.intro,
exact hq,
exact hp
end





/- ******* CONCLUSION ******* -/

/-
This unit has given an introduction to deductive
logic using natural deduction based on introduction
and elimination rules that we first saw in the unit
on propositional logic. We saw that these rules are
semantically valid (based on truth tables), and now
we take them as valid ways of deducing the truth of
propositions (conclusions) in given contexts, in 
which we have proofs of sequences of propositions 
(contexts, assumptions, premises).

As mathematicians and computer scientists, we're
often the goal of proving some putative (unproven)
theorem (aka conjecture). A key question in such
a case is what proof strategy to use to produce a
proof. The rules of natural deduction can help.
First, look at the form of the proposition. Then
ask what inference rule could be used to deduce
it. Then apply the strategy associated with that
rule.

If you want to prove an equality, simplify and
then apply the axiom that says that identical
terms can be considered equal without any other
proofs at all. If you want to prove a conjunction,
obtain proofs of the conjuncts, then deduce by
"and introduction" the desired result. If you
want to prove an implication, P → Q, explain 
how the assumption that you're given a proof
of P enables you to construct a proof of Q (or
if you're using a tool like Lean, do this in a
precise way by writing a function).

Proof strategies emerge from the choices of
inference rules needed to produce a final result.
If you already have proofs of all premises for 
a rule, just apply the rule. But in many cases,
you don't. 

The twist is to read inference rules not from top 
to bottom: if I know these things then I can 
conclude that. Instead, read them backwards: 
from bottom to top: if I want to prove this,
then it will suffice to prove these other things, 
the premises, because if I have proofs of those 
things, then I can apply this inference rule 
to get the final proof that I want.

In this way, the problem of proving a complex
conjecture is decomposed into simpler problems,
to prove each of the premises. You then apply 
this idea recursively to each premise, selecting
a proof strategy appropriate for its form, and
working backwards in this way until you get to
propositions for which proofs are available with
no futher recursion. An example is 0=0. We can
get a proof of this using rfl without any 
futher "backward chaining." Once you've worked
all the way back to propositions for which you
have "base case" proofs, you then apply the
inference rules going forward, to build the
desired proof from all of the elementary and
intermediates proofs, until, voila, you have
what you need.

As an example, consider 1=1 ∧ 0=0. It's a 
conjunction. A conjunction can be proved 
using and.intro. It, however, requires proofs
of the conjuncts. So now we need proofs of 
1=1 and of 0=0. Considering each of these 
"sub-goals" recursively, we can obtains proofs
without futher recursion, using rfl. Given 
those proofs we can combine them going
forward using and.intro. And that's how it
works. Proving theorems in this way is thus
in effect an exercise in what amounts to 
"top-down structured programming," but
what we're building isn't a program that we
intend to *run* but a proof that, if it type
checks, witnesses the truth of a proposition.
-/
theorem t5: 1=1 ∧ 0=0 := and.intro rfl rfl



/- ****** GENERALIZING PROPOSITIONS ******* -/

/-
In Lean we can declare variables to be of given
types without actually defining values for them.
You can think of these as "assumptions." So for
example, you can say, "assume that P, Q, and R 
are arbitrary propositions (of type Prop)".
-/
variables P Q R: Prop

/-
If we wanted to, we could also assume that we
have proofs of one or more of these propositions
by declaring variables to be of these types. 
Here's one example (which we won't use futher
in this code).
-/
variable proof_P: P

/-
Now we can write somewhat more interesting 
propositions, and prove them. Here's an example
in which we prove that if P ∧ Q is true then we
P is true. The proof is by the provisioning of
a function that given a proof of P ∧ Q returns
a proof of P by applying and.elim_left to its
argument.
-/
theorem t6: P ∧ Q → P :=
  λ PandQ: P ∧ Q, and.elim_left PandQ

/-
Similarly we can prove that P ∧ Q → Q ∧ P
-/
theorem t7: P ∧ Q → Q ∧ P :=
  λ PandQ: P ∧ Q, 
    and.intro 
        (and.elim_right PandQ) 
        (and.elim_left PandQ)

/- Arrow Elimination-/

theorem ae: (P → Q) -> P -> Q :=
    λ pf_impl: (P → Q), (λ pf_P: P, pf_impl pf_P)
/-
EXERCISES
-/

/-
(1) Write an implementation of comp (call 
it comp'), using a lambda expression rather
than the usual function definition notation.
This problem gives practice writing function
bodies as lambda expressions.
-/



/-
(2) Write three test cases for comp' and
generate proofs using the strategy of
"simplication and the reflexive property 
of equality."
-/



/-
(3) Implement the Fibonacci function, fib, 
using the usual recursive definition. Test
it for n = 0, n = 1, and n = 10, by writing 
and proving theorems about what it computes 
(or should compute) in these cases. Hint: 
Write your cases in the definition of the 
function for 0, 1, and n+2 (covering the
cases from 2 up). Here you get practice
writing recursive functions in Lean. The
syntax is similar to that of the Haskell
language.
-/


/-
(4) Uncomment then complete this proof of the
proposition, "Hello World" = "Hello" + " World"
(which we write using the string.append function).
Put your anwer in place of the <answer> string.
This example introduces Lean's string type, which
you might want to use at some point. It also gives
you an example showing that rfl works for diverse
types. It's polymorphic, as we said.
-/
--theorem hw : "Hello World" = string.append "Hello" " World" := <answer>


/- 
(5) Prove P ∧ Q ∧ R → R . Hint: ∧ is right-associative. 
In other words, P ∧ Q ∧ R means P ∧ (Q ∧ R). A proof of
this proposition will thus have a pair inside a pair.
-/



/-
(6)
Prove P → Q → (P ∧ Q). You can read this as saying
that if you have a proof of P, then if you (also) have
a proof of Q ,then you can produce a proof of P and Q.
Hint: → is right associative, so P → Q → (P ∧ Q) means
P → (Q → (P ∧ Q)). A proof will be a function that
takes a proof of P and returns ... you guessed it, a
function that takes a proof of Q and that returns a
proof of P ∧ Q. The body of the outer lambda will thus
use a lambda.
-/



/- EXTRA KUDOS!

Prove (P ∨ Q) → (P → R) → (Q → R) -> R. This looks
scary, but think about it in the context of material
you've already learned about. It say that if you have
a proof of (P ∨ Q), then if you also have a proof of 
(P → R), then if you also have a proof of (Q → R), then
you can derivea proof of R. The "or elimination" rule 
looked like this. You'll want to use that rule as part
of your answer. However, the  form of the proposition 
to be proved here is an implication, so a proof will 
have to be in the form of be a function. It will take 
the disjunction as an argument. Then just apply the or 
elimination rule in Lean, which is written as or.elim.
-/ 



/-
For fun and insight, check the type of orelim, the
proposition we just proved. Notice how P, Q, and R
are generalized to be *any* propositions at all. 
-/