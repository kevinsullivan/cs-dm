/-
A predicate is a "proposition with
parameters." For example, a predicate,
fromCharlottesville(p) has a parameter,
p, and asserts that p (for some value
of p) is from Charlottesville.
    
In Lean, we represent a predicate as
a function that takes one or more more 
arguments and reduces to a proposition,
and generally to one that is "about" the
arguments that were given.

So, speaking informally, for example,
fromCharlottesville(Kevin) could be read
as the proposition "Kevin is from Cville".
fromCharlottesville(Mary) is a different
proposition, "Mary is from Cville." A
predicate thus gives rise to a whole
family of propositions, one for each
possible combination of argument
values.

Not every proposition derived by applying
a predicate to one or more arguments will 
be true. Rather, the predicate in effect
"picks out" the argument values for which
the corresponding proposition is true, and
thereby identifies them as having a 
property of interest, such as the property
of "being from Cville." 
-/

/-
Consider a predicate called even(n): that, 
for any given natural number value of n, 
asserts that n is even. Given a specific 
value for n, say 3, this predicate would 
reduce to the proposition (even 3), a
proposition that asserts that 3 is even. 
Of course 3 isn't even, so (even 3) is 
false; but (even 4), on the other hand,
is true, as long as even(n) is properly
defined to express the property of being
even. The key idea is this: the numbers 
that have the property are exactly the
numbers for which the corresponding
propositions are true. The predicate
"picks out" the set of numbers with the
given property.
-/

/-
Here's one way to define an evenness
predicate. It uses the existential 
quantifier, ∃, which we study in detail
in the next unit. You can read this as
saying n is even if there exists an m
such that 2 * m = n. 
-/
def isEven (n :ℕ) : Prop :=
  ∃ m, 2 * m = n

/-
Note: isEven isn't a proposition, it's
a property!
-/

#check isEven

/-
On the other hand, (isEven 6) is a 
proposition, namely the proposition
that there is some value, m, such 
that 2 * m = n. 
-/

#reduce isEven 6

/-
We can even prove it.
-/

example : isEven 6 :=
begin
apply exists.intro 3,
apply rfl,
end


/-
We define a predicate as a function 
that takes one or more arguments and
that returns a proposition that, in
general, involves those values. 

Consider the following simple example:
a predicate that expresses the property
of a natural number of "being equal to
zero." We write this predicate as a 
function that takes a natural number, 
n, and returns the proposition that 
that number is equal to zero.

Here's such a predicate/function. 
-/

def isZero (n : ℕ): Prop := (0 = n)

/-
First, let's check the type of the 
isZero predicate. 
-/

#check isZero

/-
The type of isZero is ℕ → Prop. It is 
absolutely clear that a predicate is 
not a proposition, but is instead a 
function that takes one or more values
as arguments (here just one) that that 
reduces to a proposition. In general,
such a proposition is "about" those 
values. It asserts that they have some
particular property. 

Such a proposition need not be true, 
and will not be true if the arguments 
do not have the property in question.

For example, (isZero 3) is false. On
the other hand, (isZero 0) is true.
-/

example : isZero 0 := rfl

example : ¬(isZero 3) := 
    λ zeq3, nat.no_confusion zeq3

example : ¬(isZero 1) := 
begin
  assume zeq1,
  exact nat.no_confusion zeq1
end

/-
Think carefully about what kind of value
this predicate/function returns when 
applied to a particular argument value,
e.g., 3. The result is a proposition, 
in particular, a proposition about 3, 
namely one that asserts that 0 = 3.

To be clear, isZero is a predicate:
a function from a ℕ-valued argument 
to Prop. By contrast, (isZero 3) is 
a proposition. Look at the types of
the following expressions.
-/

#check isZero 0 -- a proposition 
#check isZero 1 -- a proposition 
#check isZero 2 -- a proposition 

/-
Now look at the specific propositions
that this predicate/function returns
when applied to particular arguments.
Study this until it's clear to you that
applying a predicate to an argument 
returns a proposition about that value.
-/

#reduce isZero 0 -- the proposition 0 = 0
#reduce isZero 1 -- the proposition 0 = 1
#reduce isZero 2 -- the proposition 0 = 2

/-
We can rewrite this function into
an equivalent form in the usual way,
to make the type of the predicate
clear as a function type. The type
of isZero is ℕ → Prop. 
-/

def isZero' : ℕ → Prop := 
    λ n, 0 = n

/-
Again, you can think of a predicate 
as specifying a *property* of its
argument: in this case the property 
of "being equal to zero". Argument
values for which the corresponding
propositions are true have the given
property, and those for which the
corresponding proposition is false,
do not have the property. 
-/

-- 0 has the isZero property
theorem zeqz : isZero 0 :=
    eq.refl 0

-- 1 does not have this property
theorem oneeqz : ¬(isZero 1) :=
begin
  unfold isZero,
  assume eq,
  exact nat.no_confusion eq,
end

/-
A predicate basically asserts that 
the value given as its argument has 
some property. Not every value has a 
given property (e.g., 3 does not have 
the property of being even). In general 
a given predicate is not true for 
every value of its argument(s).

EXERCISE: What are other properties
of natural numbers that could be
expressed as predicates?

EXERCISE: Define a predicate that is
true for every natural number.

EXERCISE: Define a predicate that is
false for every natural number.
-/

def is_absorbed_by_zero(n: ℕ): Prop := n * 0 = 0

def equals_self_plus_one(n: ℕ): Prop := n = n + 1

/-
EXAMPLE: Thank goodness it's the
weekend.

Below we define a new datatype,
day, with the names of the seven
days of the week as values. Given
this datatype, specify the property
of being a weekend day.
-/

inductive day : Type
| Monday
| Tuesday
| Wednesday
| Thursday
| Friday
| Saturday
| Sunday

#check day.Tuesday

open day -- no longer need to day. prefix

#check Tuesday


-- Answer

def isWeekend : day → Prop :=
    λ d, d = Saturday ∨ d = Sunday


-- EXERCISE: Show Saturday's a weekend day
theorem satIsWeekend: isWeekend Saturday :=
begin
  unfold isWeekend,   -- unfold tactic
  apply or.intro_left,-- backwards reasoning
  apply rfl           -- finally, equality
end


/-
As a final important concept that we just
introduce in this section, we note that we
can think of a predicate as specifying a
set of values: the set of values for which 
the predicate (corresponding proposition)
is true. 

For example, the predicate, isZero(n),
specifies the set containing only the 
natural number, zero. A predicate, 
isEven(n), could specify the set of 
even natural numbers. Etc. We explore
this idea in more depth in the unit on
sets to come shortly. 

EXERCISE: Think of a few more
properties that you could specify 
as predicates. What are the domains
of values on which your properties
are defined? What sets do your
predicates define?
-/
