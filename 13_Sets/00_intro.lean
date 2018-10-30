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

/-
The proposition that an element,
e, is in (is a member of) a set,
s, is written e ∈ s. We can thus 
assert, and we can then actually 
prove, that 1 is in the set, x.
-/

example : 1 ∈ x :=
-- 1 = 1 ∨ false
begin
apply or.intro_left,
exact rfl,
end

example : 1 ∈ x' :=
-- 1 = 1
begin
exact rfl,
end

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

example : 3 ∈ y ∪ z :=
begin
apply or.inl,
apply or.inl,
exact rfl
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
begin
apply and.intro,
apply or.inr,
apply or.inl,
exact rfl,
apply or.inr,
apply or.inr,
apply or.inl,
exact rfl,
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
apply and.intro,
apply or.inr,
apply or.inr,
apply or.inl,
exact rfl,
assume pf,
cases pf,
sorry,
cases pf,
sorry,
cases pf,
sorry,
sorry,
end

/-
We're going to show you how to get a 
version of Lean that includes the math
library, which you need to make these
proofs go through easily without sorrys.
Soon.
-/