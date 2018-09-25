/-
We've met but haven't yet been
properly introduced to ∀. 

Assuming P and Q are propositions,
What does (∀ p : P, Q) mean?

For example, what does this mean?

    ∀ n : nat, n + 1 ≠ 0

First, you can read ∀ n : nat 
"for all values, n, of type nat."
This proposition thus asserts that, 
for all natural numbers, n, of type
nat, (i.e., "for any natural number, 
n") the successor of n is not 0.

More generally, with P as any type,
and Q as a proposition, (∀ p : P, Q)
states that for every value, p, in 
the set of values defined by the type, 
P, one can derive a proof of Q. 

Here's our concrete example stated 
and proved in Lean.
-/

example : ∀ n : nat, n + 1 ≠ 0 :=
    -- assume an arbitrary nat, n
    λ n : nat,    
        -- assume proof of n + 1 = 0
        λ h : (n + 1 = 0), 
            -- derive a contradiction
            (nat.no_confusion h : false)
    -- therefore n + 1 ≠ 0

/-
Here's another example, which you
have seen before (without a proof).
It says that for any proposition, 
P (in the set of all propositions
defined by the type, Prop), it is 
not possible to have both P and 
¬ P be true at the same time.
-/

example : ∀ P : Prop, ¬ (P ∧ ¬ P) :=
    -- assume an arbitrary proposition
    λ P : Prop,
        -- assume it's both true and false
        λ h : (P ∧ ¬ P),
            -- derive a contradition
            (h.right h.left : false)
    -- thereby proving ¬ h

/-
The ∀ parts of these propositions, 
before the commas, give names to
arbitrary elements of a type. The
parts after the commas then state
a claim (that is usually) about the
named element.

Look at the preceding examples. In
the case of ∀ n : nat, n + 1 ≠ 0, the
part before the comma asserts that
the proposition following the comma
is true of any arbitrary (and thus 
of every) element, n, of type nat.

We say that the ∀ "binds" the name
to an arbitrary value of the given
type. The binding is operative for 
the remainder of the  proposition. 

We note that successive bindings
accumulate, defining a context in
which the remainder of a proposition
is stated and proved. 

Here's an example that states that
for any two natural numbers, n and
m, either n = m or n ≠ m. We use the
connective, ∨, to denote disjunction
(logical or). More about that later.
We "stub out" the simple proof for
now.
-/

example : ∀ n : nat, ∀ m : nat, 
    m = n ∨ m ≠ n := 
begin
    assume n : nat,
    -- the context now includes n
    assume m : nat,
    -- the context now also has m
    sorry
end
-- the bindings no longer hold here


/-
So that should give an understanding
of the use and meaning of the univeral 
quantifier, ∀, in predicate logic.

What does (∀ p : P, Q) mean in the
constructive logic of Lean?

Let's check! First we'll assume two
arbitrary propositions, P and Q, and
a proof of ∀ p : P, Q. Then we can ask
what is the type of ∀ p : P, Q. It is
a proposition, after all, and in Lean,
propositions are types. What type is 
it?
-/

-- Assume P and Q are propositions
variables P Q : Prop

-- What is the type of (∀ p : P, Q)
#check (∀ p : P, Q)

/-
What? the proposition/type, 
(∀ p : P, Q) is really just
the proposition/type, P → Q.
-/

/-
If that's true, we should be able 
to assume proof of (∀ p : P, Q)
and then use it as a function. 
Let's see.
-/

-- Assume a proof of ∀ (p : P), Q.
variable ap2q : (∀ p : P, Q)

-- Assume a proof of P.
variable p : P

-- What is the type of (ap2q p). Q
#check ap2q p

-- They're the same types! Here's a proof.
theorem same : (∀ p : P, Q) = (P → Q) := rfl

/-
So why not just use → instead of ∀? The
answer is that ∀ let's us bind a name to
an assumed value, a name that we can then
use in the remainder of the expression.
The → connective doesn't let us bind a
name to a value. 

The following example thus defines a type 
of function that, given a natural number, 
n, reduces to (returns) the proposition
that that particular n is either 0 or not
0. This is a function type. 
-/

#check ∀ n : nat, n = 0 ∨ n ≠ 0.


/-
A proof of this proposition/type is then
a function that, if given any nat value, n,
returns a value of type (a proof that) that
particular n is either 0 or not 0.

The binding of a name to an assumed value
effected by a ∀ provides us a context in 
which we can state the remainder of the
universally quantified proposition. 
-/


/- ** Further explanation ** -/

/-
So now we can see at least three ways to
read (∀ p : P, Q).

(1) As a universally quantified logical 
proposition. As such, it asserts that if
p is any value of type P, then from it
one can derive a proof of the proposition,
Q, which will typically involve p. 


(2) As a logical implication, P → Q. This
is read simply as P implies Q. 

(3) As the type of total functions from 
P to Q. 

By a total function, we mean a function 
that is defined "for all" values of its 
argument types. It cannot be a "partial"
function that is undefined on some values
of its argument type. 

The concepts of "for all" and of total
functions are intimately related here.
The ∀ explicitly requires that such a 
function be defined "for all" values of
the designated type.

That functions are total is fundamental 
to constructive logic. We will explain
why later.
-/



/- ** Further examples ** -/

/- 

#1. Nested ∀ bindings.

Let' assume we have another proposition, R.
-/

variable R : Prop

/-
So, what does this mean: ∀ p : P, ∀ q : Q, R?
The ∀ is right-associative so we read this as 
∀ p : P, (∀ q : Q, R). Using what we learned 
above, we can see that it means P → Q → R!
-/

#check ∀ p : P, (∀ q : Q, R)

/-
There are at least three ways to think about
this construct.

(1) It is the universally quantified proposition 
that holds that if one assumes any proof P and 
then further assumes any proof of Q, then in 
that context one can derive a  proof of R. 

(2) It is the logical proposition, P implies
Q implies R, written as P → Q → R.

(3) Is it the function type, P → Q → R. As
we've discussed, → is right associative, 
so this is the function type is P → (Q → R). 
-/


/- ** Chained implications ** -/

/-
What is the function type, P → Q → R? It
is the type of function that takes a value 
of type P as an argument and reduces to a
function of type (Q → R), a function that
takes a value of type Q, and that finally 
reduces to a value of type R.

Of course, you can just think of this as a
function that takes two arguments, the first
of type P and the second of type Q, and that
then reduces to a value of type R.

In fact in Lean and in most functional 
languages, you can treat any function that 
takes multiple arguments as one that takes 
one argument (the first) and then reduces 
to a function that takes the next argument,
and so on until the last argument has been
consumed, at which point it reduces to a
result of the type at the end of the chain. 

Let's look at an example involving the 
+ operator applied to two natural numbers.
The + operator is a shorthand for nat.add.
-/

#check nat.add 2 3
#check (nat.add 2) 3 -- same thing
#check nat.add 2
#check nat.add

/-
Function application is left-associative.
Here, for example, nat.add consumes a 2 in
the first line and reduces to a function
(one that "bakes in the 2") that consumes 
the 3 and finally reduces to 5.
-/

/-
#2

Let's return to an example we saw on the
recent in-class no-contradiction exercise:
no_contradiction: ∀ P : Prop, ¬ (P ∧ ¬ P). 

We can now this type as a function type for
functions that take a proposition, P, and that 
reduce to the proposition, ¬ (P ∧ ¬ P), which
is to say, to (P ∧ ¬ P) → false. We thus have
a function type like this:

(P : Prop) → (P ∧ ¬ P) → false.

But we can't write it like that because Lean
doesn't allow us to bind names to value in this
way. We have to use ∀ instead.

∀ P : Prop, (P ∧ ¬ P) → false.

Nevertheless, if we have a value of this type,
it will be a function whose first argument is
any proposition. Let's see this in action. 
-/

-- Assume a proof/function of the given type
variable no_contra : ∀ P : Prop, ¬ (P ∧ ¬ P)

/-
Now look at what we get when we apply this 
function to any proposition, P. We get back 
a value of type (the proposition), P ∧ ¬ P.
-/

#check no_contra (0 = 0)
#check no_contra ¬ P
#check no_contra (P → Q)

/-
Of course each of the results is a value
of type ¬ (P ∧ ¬ P), which is to say it's
another function: from proofs of (P ∧ ¬ P)
to false. 

For a little (logic-destroying) fun,let's 
assume we have a proof of 0 = 0 ∧ ¬ 0 = 0 
and produce a proof of false. 
-/

-- Assume a proof of  0 = 0 ∧ 0 ≠ 0,
variable inconsistency : 0 = 0 ∧ 0 ≠ 0

--Apply the function, contra (0 = 0), to it
#check (no_contra (0 = 0)) inconsistency

/-
Voila! A proof of false. Of course we
never could have constructed it without
having made an absurd assumption.
-/


/-
   ** Conclusion **
-/

/-
Now we know that (∀ p : P, Q) means P → Q, 
but it also binds a name to an assumed value
of type P that we can use in expressing Q.
An easy way to think about this is that a
binding of a name to a value of type P is
exactly like the declaration of an argument
to a function, and Q is like the body of 
the function in which the name P can be
used.
-/
