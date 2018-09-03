/-
Predicates
-/

def isZero (n: nat) := n = 0 ∨ false

/-
isZero 3 -- 3 = 0   N
isZero 1 -- 1 = 0   N
isZero 0 -- 0 = 0   Y
isZero -1 -- type error
-/

/-
or.introduction 
-/

theorem o1 : 0 = 0 ∨ 0 = 1 := 
    or.intro_left (0 = 1) (eq.refl 0)

#check (isZero 3)
#reduce isZero 3
theorem foo: isZero 0 :=  
    or.intro_left 
        (0 = 1) (eq.refl 0)

/-
Predicates are programs.
They take arguments and
reduce to propositions about
those arguments. These 
propositions in turn might 
or might not be true (have 
proofs.)
-/

/-
We've seen here a first
example of a program in Lean.
Let's write another one. How
about a program that takes 
a natural number and returns
that number + 1.
-/

def inc (n : nat) := n + 1

#reduce inc 3

/-
There's another important
notation for programs that
is incredibly useful, not
only here in Lean but in
functional programming more
generally and now even in
languages such as Java and
C++. By the way, the highest
paid programmers today are
those who understand deeply
functional programming.

Let's look at an alternative
notation for inc. We'll call
our new version inc'.
-/

def inc' := λ n : nat, n + 1

/-
The way to pronounce lambda is
"a program that takes a parameter ...
(of type ...), ... and that returns 
the value of the expression ..."
-/

#reduce inc' 3

/-
EXERCISE: Re-write isZero using
lambda notation. Call the new
program isZero'.
-/

def isZero' :=  λ n, n = 0

#reduce isZero'

/-
Predicates encode properties.
Here the it's a property of a
single natural number, namely
the property of being equal to
zero. For every argument value
that has that property, there
is a proof, and there are no
proofs for any other values.

We could even say that there 
is a set of natural numbers 
that has this property. It is
of course the set, { 0 }.
-/

def aSet: set nat := { 0 }

#check aSet

lemma xyz : aSet = isZero := rfl

#reduce aSet

/-
If you really think about this a predicate
such as isZero is very much like a program
that takes an argument and returns a
proposition that in general will include 
that argument value as an element.
-/