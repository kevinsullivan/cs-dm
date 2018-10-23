/-
As discussed in the last unit, a 
predicate is a proposition with
one more more arguments. 

In the last unit, we studied 
predicates with one argument. We 
saw that such a predicate can be 
seen as specifying a *property* 
of values of its argument type.
Examples included the properties
of being even, being equal to 0,
being a perfect square, or of (a
person) being from Cville. 

We now look at predicates with
multiple arguments. We emphasize
the idea that such predicates can
be used to specify properties of 
*tuples* (e.g., pairs) of values. 
We refer to properties involving 
tuples as relations.

As an example we can consider 
equality as a relation between
two values. A relation involving
two values is said to be a binary
relation. We could represent the 
"equals" relation as a predicate 
with two arguments, n and m, and
rules that provide proofs of the
proposition "equals m n" if and
only if m = n. We can represent 
this predicate as a function 
that now takes two arguments and 
returns Prop.
-/

def areEqual : ℕ → ℕ → Prop :=
    λ n m, n = m

#check areEqual 0 0
#reduce areEqual 0 0

lemma zeqz : areEqual 0 0 := eq.refl 0

#check areEqual 2 3
#reduce areEqual 2 3

/-
Be sure you're comfortable with
these ideas. We define areEqual
as a function that takes n and m as
arguments (of type ℕ) and that then
returns the *proposition*, n = m.
Be clear that this function does 
NOT return a proof. It returns a
proposition that might or might 
not be true! 

The single predicate, which most
mathematicians would write as 
areEqual(n,m), with two arguments,
defines an infinity of propositions,
each one about one specific pair of
natural numbers. 

Some of these propositions have 
proofs and thus are true. Others 
do not, and are not true. Such a
predicate thus "picks out" a subset
of all possible pairs, namely those
for which its proposition is true.
These pairs include (0, 0) but not
(2, 3). 

Such a set of pairs is what we think 
of as the relation that the predicate
specifies. In particular, areEqual
specifies a "binary" relation, the
set of all pairs of natural numbers
that are equal to themselves. 

Let's prove that a few elements are
in, and that another one is not in,
the areEqual(n,m) relation.
-/

-- (1, 1) is in the relation
example : areEqual 1 1 :=
    eq.refl 1

-- (2, 2) is in the relation
example : areEqual 2 2 :=
    eq.refl 2

-- but (0, 1) is not in it
example : ¬(areEqual 0 1) :=
    λ zeqo, nat.no_confusion zeqo


/-
EXERCISE [Worked]: Define a predicate
isSquare that expresses the relation
between two natural numbers that the
second natural number is the square
of the first and prove that the pair,
(3, 9), is in the isSquare, relation.
-/

-- Answer

def isSquare: ℕ → ℕ → Prop :=
    λ n m, n * n = m

example : isSquare 3 9 :=
begin
unfold isSquare,
exact rfl,
end



/-
EXERCISE: In lean, the function,
string.length returns the length
of a given string. Specify a new
predicate sHasLenN taking a string
and a natural number as arguments
that asserts that a given string
has the given length.  Write the
function using lambda notation to
make the type of the predicate as
clear as possible.
-/

#eval string.length "Hello"




-- answer here

def sHasLenN (s :string) (n : ℕ) : Prop :=
    s.length = n

example : sHasLenN "Hello" 5 := 
begin
unfold sHasLenN,
exact rfl,
end



def pythagoreanTriple : ℕ → ℕ → ℕ → Prop :=
    λ a b h, a^2 + b^2 = h^2

example : pythagoreanTriple 3 4 5 :=
begin
unfold pythagoreanTriple,
exact rfl,
end 