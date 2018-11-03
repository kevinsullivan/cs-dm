/-
In Lean, set is a type constructor. It takes
a type, T, as an argument and returns, as a 
result, the type, set T, which  we read as the
type of any set with elements of type, T. The
type of set is thus Type → Type. Lean tells
us that this type constructor can take a type
in any type universe, i.e., Type, Type 1, etc.
We needn't be concerned with that here.
-/

#check set

/-
EXERCISE: Is set a type? Discuss.
-/

#check set nat

/-
The type, set nat, or set T more 
generally, represents a property
of value of type nat (or T): the
property of "being in a given set!"
-/

#reduce set nat

/-
We now define e to be the empty
set of natural numbers. Lean gives
us ordinary set display notation
(using curly braces around a list
of elements) for this purpose.
-/

def e: set nat := { }

/-
The symbol, ∅, is often used
to represent the empty set (of
values of some type).
-/

def e': set nat := ∅ 

/-
We can't just say "e : set := {}"",
because then Lean does not have 
enough context to infer the type
of the elements.
-/

/-
EXERCISE: What is the property of 
natural numbers that characterizes 
the empty set of natural numbers?
-/

#reduce e

/-
Study that carefully. The predicate 
that defines the empty set is, as
we've alreadydiscussed, false(n):
i.e., the function of type ℕ → Prop
that for any value, n : ℕ, returns
the proposition false. No natural
number can makes the (proposition
derived from the) predicate true, 
so no natural number is in the set
that it represents.
-/

/-
We can also represent the empty 
set using set builder notation.
-/

def e'' : set nat := { n | false }

def ev(n : ℕ):Prop := ∃ m, m + m = n 

def v : set nat := { n | ev n } 
/-
We read the right hand side as
"the set of values, n, for which
the predicate, false, is true."
As there is no value that makes
false true, the set is empty. It
has no elements.
-/

/-
Here's another set of ℕ, containing 
only the number, 1. We call such a
set a singleton set.
-/

def x: set nat := { 1 }

/-
EXERCISE: What property of natural 
numbers defines the property of being 
in this set? Try to come up with the
answer before you look! 
-/

#reduce x

/-
The answer is a little surprising.
The predicate λ n, n = 1, would do
to define this set, but instead Lean
uses λ n, n = 1 ∨ false. The basic
intuition is that, were we to remove
the 1 from this set, we'd be left 
with the empty set, the predicate
for which is that predicate false.
-/

def x' := { n | n = 1 }

#reduce x'

/-
The two notations give rise to
slightly different but equivalent
predicates.
-/

-- SET MEMBERSHIP

/-
By the notation 1 ∈ x we mean the
proposition that "1 is in, or is 
a member of the set, x." This is
simplythe proposition obtained 
by applying the predicate, x, to
the value, 1. The proposition is
literally the value (x 1). Recall 
that function application works 
by substituting the argument (1)
for the parameter (a) in the body 
of the predicate (function).  In
this case, the predicate, x, is
λ (n : ℕ), n = 1. Applying this
predicate/function the value, 1,
reduces to the proposition that:
1 = 1 ∨ false. This proposition,
in turn, is easy to prove, and so,
yes, indeed, 1 is in the set x.
-/

#reduce 1 ∈ x

example : 1 ∈ x :=
-- 1 = 1 ∨ false
begin
apply or.intro_left,
exact rfl,
end

/-
Because the proposition, 1 ∈ x,
is defined to be the disjunction,
(1 = 1 ∨ false), you can ask Lean 
to change the format of the goal 
accordingly. If doing this makes 
it easier for you to see how to 
proceed with the proof, feel free 
to use it. You can cut and paste
the disjunction from the string
that #reduce 3 ∈ u prints out.
-/


example : 1 ∈ x :=
-- 1 = 1
begin
change 1 = 1 ∨ false,
-- now or.intro_left, but with a shortcut
left,
-- and now exact rfl, but with a shortcut
trivial,
end


-- ANOTHER EXAMPLE

/-
Here's two sets with three
elements each.
-/

def y : set nat := { 1, 2, 3 }
def z : set nat := { 2, 3, 4 }

/-
EXERCISE: What is a predicate
that characterizes membership in
the set, y?
-/

#reduce y


/-
EXERCISE: Define the same set, y,
with the name, y', using set builder
notation.
-/

def y' : set nat := { n | 
    n = 1 ∨ n = 2 ∨ n = 3 }

#reduce y 

/-
With these basics in hand, we can 
define, understand, and work with
the full range of set operations.
Set operations are like operations
with numbers but their operands and
results are sets.
-/

-- SET UNION

/-
The union of two sets, y and z, 
which we denote as y ∪ z, is the
combined set of values from y and 
z. 

An element is either in or not in 
a given, but cannot be in a more 
than one time (otherwise you have
what is called a multiset). The 
union of y and z as defined above 
is thus the set { 1, 2, 3, 4 }.
-/

def u := y ∪ z


/-
EXERCISE: What predicate defines 
the set that is the union of y and z?
-/

#reduce u

/-
Answer: It is the predicate that
defines what it means to be in y 
or to be in z. That is, it is the
disjunction of the predicates that
define y and z, respectively. Union
corresponds to "or."
-/

/-
Let's prove that 3 ∈ u. Let's 
start by reminding ourselves of
the predicate that defines u and
of the proposition represented 
by 3 ∈ u.
-/

#reduce u

/-
The set, u, is defined as a
predicate that takes a : ℕ and
returns the proposition that
that a is one of the values
in the set, expressed as a 
somewhat long disjunction. Lean 
selects the variable name, a, 
for purposes of printing out 
the value of u. There is no
special meaning to a; it is 
just an otherwise unbound name.
-/


/-
Now that we know that 3 ∈ u is 
just a proposition involving a
bunch of disjunctions, it's easy
to prove. -/

example : 3 ∈ u :=
begin
/-
Notice again that Lean leaves the 
goal written using set membership
notation. Just bear in mind that
the goal is just the disjunction,
(3 = 3 ∨ 3 = 2 ∨ 3 = 1 ∨ false) ∨ 
3 = 4 ∨ 3 = 3 ∨ 3 = 2 ∨ false.
-/
left,
left,
trivial,
end

/-
Or, if you prefer, make the goal
explicit as a disjunction.
-/
example : 3 ∈ y ∪ z :=
begin
change (3 = 3 ∨ 3 = 2 ∨ 3 = 1 ∨ false) ∨ 3 = 4 ∨ 3 = 3 ∨ 3 = 2 ∨ false,
apply or.inl,
apply or.inl,
trivial,
end

-- SET INTERSECTION

/-
The intersection of two sets, y and
z, which we denote as y ∩ z, is the
set containing those values that are
in y and that are in z. Intersection
thus corresponds to the conjunction
of the predicates defining the two
individual sets.
-/

def w := y ∩ z

#reduce w

example : 2 ∈ y ∩ z :=
-- (a = 3 ∨ a = 2 ∨ a = 1 ∨ false) ∧ (a = 4 ∨ a = 3 ∨ a = 2 ∨ false)
begin
apply and.intro,
right,
left,
trivial,
right,
right,
left,
trivial,
end


-- SET DIFFERENCE

/-
The set difference y - z, also
writen as y \ z, is the set of
values that are in y but not in
z. Think of the subtraction as
saying that from y you take away
z, and the result is what is left
of y.

EXERCISE: What predicate defines
a set difference, y \ z?
-/

#reduce y \ z

example : 1 ∈ y \ z :=
begin
-- apply and.intro,
split,
right,
right,
left,
trivial,
/-
The goal looks funny, but think
about what it means. It is the
predicate, (λ (a : ℕ), a ∉ z),
applied to the value, 1, which
is to say it's the proposition,
1 ∉ z. That in turn is ¬ 1 ∈ z.
And that, in turn, is just the
proposition that 1 ∈ z → false.
So assume 1 ∈ z and show false 
to prove it. What is 1 ∈ z? It's
the proposition that 1 is one of
the elements in the set, written
as a disjunction, so use case
analysis! 
-/
assume pf,
cases pf,
/-
Now we need a proof that 1 ≠ 4. The 
dec_trivial tactic defined in the Lean's
standard library "decides" many purely 
arithmetic propositions. That is, it 
generates either a proof that such a
proposition is true if it's true. It
will also generate a proof that its
negation is true if that is the case. 
The dec_trivial tactic implements a
"decision procedure" for sufficiently
simple propositions involved numbers.
Here we use it to give us a proof of 
1 ≠ 4. We can then use that to get a 
proof of false and use false elim to 
eliminate the current case on grounds 
that it is based on contradictory
assumptions (and thus can't happen).
-/
have h : 1 ≠ 4 := dec_trivial,
/-
The contradiction tactic looks for a
explicit contradiction in the context
and if it finds one, applies false.elim
to finish proving the goal.
-/
contradiction,
cases pf,
have h : 1 ≠ 3 := dec_trivial,
contradiction,
cases pf,
have h : 1 ≠ 2 := dec_trivial,
contradiction,
have f : false := pf,
contradiction,
end

-- SUMMARY SO FAR

/-
A set can be characterized by
a predicate: one that is true
for each member of the set and
false otherwise.

The union of two sets is given
by the disjunction (or) of the 
predicates:
(a ∈ y ∪ z) = (a ∈ y) ∨ (a ∈ z)

The conjunction is defined by 
their conjunction:
(x ∈ y ∩ z) = (x ∈ y ∧ a ∈ z)

Their difference is defined by 
the conjunction of the first and
the negation of the second:
(a ∈ y \ z) = ( a ∈ y) ∧ (¬ a ∈ z)
-/

-- PART II

/-
Now we introduce addition basic 
set theory concepts: subsets,
power sets, and product sets.
-/

-- Subset

/-
Subset, denoted ⊂, is a binary 
relation on sets, denoted X ⊂ Y, 
where X and Y are sets, that is 
true iff every element of X is 
also in (an element of) Y. 

So, { 1, 2 } ⊂ { 1, 2, 3 } but
¬ { 1, 2 } ⊂ { 1, 3, 4}. In the
first case, every element of the
set, { 1, 2 }, is also in the set
{ 1, 2, 3 }, so { 1, 2 } is a 
subset of { 1, 2, 3 }, but that
is not the case for { 1, 2 } and
{ 1, 3, 4 }.

Remember that in Lean, "set" is 
not a type but a type constructor,
a.k.a., a polymorphic type. Rather,
for any type, T, set T is a type,
namely the type of sets containing
elements of type T. Even the empty
set always has an element type, so,
for example, the empty set of ℕ is
not the same as the empty set of 
strings.
-/

/-
EXERCISE: List all of the subsets
of each of the following sets of ℕ. 

* ∅ 
* { 1 }
* { 1, 2 }
* { 1, 2, 3 }

EXERCISE: How many subsets are there
f a set containing n elements. Does 
your formula work even for the empty
set, containing 0 elements?
-/

theorem foo : x ⊂ y := _