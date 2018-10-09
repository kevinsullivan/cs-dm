/-
A predicate is a parameterized
proposition. You can think of it
as a function. Given a parameter 
value as an argument a predicate 
reduces to a proposition, usually 
one about that argument value.
-/

/-
A simple example is a predicate
that takes a natural number, n,
as an argument, and that reduces
to the proposition 0 = n. 
-/

def isEqZ (n : ℕ ) : Prop := 0 = n

#check isEqZ 0
#check isEqZ 1
#check isEqZ 2
#check isEqZ 3

/-
We can rewrite this function into
an equivalent form in the usual way.
-/

def isEqz' : ℕ → Prop := 
    λ n, 0 = n

/-
This expression of the concept
makes it clear that the type of
zeqn' (and of zeqn) is not Prop
but ℕ → Prop. It's a predicate,
not a proposition.
-/

/-
Predicates can be applied to 
values and used in stating 
theorems.
-/

theorem zeqz : isEqZ 0 :=
    eq.refl 0

/-
A predicate specifies a property
of the elements of the argument type
by specifying a different proposition 
about each such argument value.

Here the property is the property
(of natural numbers) of being equal 
to zero. The property is expressed
by the family of propositions that 
can be produced by isEqZ, one for 
each natural number.

In this case, only one such 
proposition is true, the one 
where n is 0, yielding the 
proposition, 0 = 0.
-/

/-
EXERCISE: Express the property, 
of natural numbers, of being a 
perfect square. For example, 9
is a perfect square, because 3
is a natural number such that 
3 * 3 = 9. By constrast, 12 is
not a perfect square, as there 
is no other natural number that
squares to 12. 
-/
