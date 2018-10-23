/- ***********************-/
/- *** ∃ Introduction *** -/
/-************************-/

/-
An existentially quantified 
proposition asserts that there
exusts *some* value of some type 
that makes a given predicate 
true. Here's an example.
-/

def anExistsProp := 
    exists m , m + m = 8

/- This proposition asserts that 
there is some value m (inferred 
to be of type ℕ) that makes the 
predicate, m + m = 8, true. 

Basic algebra tells us that there 
is such a value, namely 4, so this 
existentially quantified proposition
can be proved and is true. 

The key thing to remember is that
a proof of such an existentially
quantified proposition is a pair.

The first element is a value that 
makes the sub-proposition true. We
call such a value a "witness". In
the example, the witness is 4. 

The second element in a proof 
is a proof of that the proposition
obtained by substituting the witness
in for the value of the variable in
the predicate is true. Here, the
proof must be a proof of 4 + 4 = 8.

A proof of exists m , m + m = 8, is
thus the pair, ⟨ 4, rfl ⟩. Here we use
special angle brackets, a notation that
Lean recognizes for writing proofs of existentially quantified propositions.
-/

/-
More generally the introduction 
rule for ∃ is as follows:

{ T : Type } { p: T → Prop } (w : T) (e : p w)
----------------------------------------------
            ∃ a : T, pred a
-/

#print exists.intro

/-
Here's code that illustrates the use of
-/

def existsIntro 
(T: Type)           -- arguments
(pred: T → Prop) 
(w : T) 
(e : pred w) 
: 
exists w, pred w    -- return type
:= 
exists.intro w e    -- direct use of exists. intro

/-
Abstract example
-/
variable T : Type
variable witness : T
variable predicate : T → Prop
#check predicate witness
variable proof : predicate witness

-- direct use of exists.intro
def pfOfExists : ∃ m, predicate m := 
    exists.intro witness proof 

-- shorthand
def pfOfExists' : ∃ m, predicate m := 
    ⟨ witness, proof ⟩ 

-- a script in which we build the proof interactively
def fourAgain : exists m, m + m = 8 :=
begin
    apply exists.intro 4,
    exact rfl,
end

/-
Concrete example
-/

def isEven (n : nat) : Prop :=
    exists m : nat, m + m = n

/-
A bad definition of isEven (last time).
-/

def isEvenBadDef (n : nat) : Prop :=
    exists m : nat, n / m = 2

example : isEvenBadDef 7 :=
    ⟨ 3.5, rfl ⟩ 

-- OOPS "/"" is natural number division
#reduce (7 / 2 : nat)

-- 
def eightEven := isEven 8

#check eightEven
#reduce eightEven

-- exact proof term using exists.intro
theorem even8 : eightEven := 
    exists.intro 4 rfl

-- syntactic sugar
theorem even8' : eightEven := 
    ⟨ 4, rfl ⟩ 

-- as a tactic script
-- unfold expands a definition
theorem even8'' : isEven 8 := 
begin
unfold isEven,      -- not necessary
apply exists.intro 4,
exact rfl 
end 

/-
EXERCISE: Construct a proof, isNonZ,
of the proposition that there exists 
a natural number n such that 0 ≠ n.
-/

theorem isNonZ : exists n : nat, 0 ≠ n :=
exists.intro 1 (λ pf : (0 = 1), 
nat.no_confusion pf)
-- second arg is a pf of 0=1→false


/- **********************-/
/- *** ∃ Elimination *** -/
/-***********************-/

/-
If one assumes that ∃ x, P x, then one 
can assume there is an arbitrary value,
w, such that P w is true. If one can then 
show, without making additional assumptions 
about w, that some conclusion, Q that does
not depend on w, follows, that one has shown
that Q follows from the mere existence of a
w with property P, and thus from ∃ x, P x. 

The formal rule is a little bit involved. 
Here it is as an inference rule. We explain
each piece below.

∀ Q : Prop; ∀ T : Type; ∀ P : T → Prop; ∃ x : T, P x; ∀ w : T, P w → Q
----------------------------------------------------------------------
               Q

This rule says that we can conclude that
any proposition, Q, is true, if (1) T is
any type of value; (2) P is any property 
of values of this type; (3) there is some
value, x, of this type that has property 
P; and (4) from any such value, w, Q then
follows. 

This is the elimination rule for ∃. It 
lets you draw a conclusion, Q, from the
premise that ∃ x, P x and from a proof
that from any such w one can construct
a proof of Q.

The following function shows all of the
pieces needed to use exists.elim and how
to use it. Note that the conclusion, Q,
the type of elements involved, T, and 
the property, P, are given implicitly,
as they can be inferred from the ∃ and
from the proof that Q follows from any
such value.
-/

def existsElim 
    { Q : Prop }
    { T : Type } 
    { P : T → Prop }
    ( ex : exists x, P x) 
    ( pw2q : ∀ w : T, P w → Q) 
    : Q
    :=
        exists.elim ex pw2q


/-
EXAMPLE. Let's prove that if there
is a value of some type that has two
properties, P and Q, then it has one
of those properties.

-/

-- assume P and S are properties of nats
variables (P : ℕ → Prop) (S : ℕ → Prop)

theorem forgetAProperty : 
(exists n, P n ∧ S n) → (exists n, P n) :=
-- here Q, the conclusion, is (exists n, P n)
begin
assume ex,
show ∃ (n : ℕ), P n,
from
    begin
    apply exists.elim ex, -- give one arg, build  other
    assume w Pw,          -- assume w and proof of P w
    show ∃ (n : ℕ), P n,
    from exists.intro w Pw.left,
    end,
end

/-
*** EXERCISE: 

Prove:
Assuming n is a nat and P and S are properties of nats,
prove that (exists n, P n ∧ S n) → (exists n, S n ∧ P n).
-/

theorem reverseProperty : 
(exists n, P n ∧ S n) → (exists n, S n ∧ P n) :=
-- here Q, the conclusion, is (exists n, P n)
begin
assume ex,
show ∃ (n : ℕ), S n ∧ P n,
from
    begin
    apply exists.elim ex, -- give one arg, build other
    assume w Pw,          -- assume w and proof of P w
    show ∃ (n : ℕ), S n ∧ P n,
    -- here's some new notation for and.intro
    from exists.intro w ⟨ Pw.right, Pw.left ⟩ 
    end,
end

/-
EXAMPLE: Express the property, 
of natural numbers, of being a 
perfect square. For example, 9
is a perfect square, because 3
is a natural number such that 
3 * 3 = 9. By constrast, 12 is
not a perfect square, as there 
is no other natural number that
squares to 12. 

State and prove the proposition 
that 9 is a perfect square.
-/

-- Answer

def isASquare: ℕ → Prop :=
    λ n, exists m, n = m ^ 2

theorem isPS9 : isASquare 9 
:=
begin
unfold isASquare,
exact exists.intro 3 (eq.refl 9)
end


/-
EXERCISE: In lean, the function,
string.length returns the length
of a given string. Specify a new
predicate sHasLenL taking a string
and a natural number as arguments
that asserts that a given string
has the given length.  Write the
function using lambda notation to
make the type of the predicate as
clear as possible.
-/

#eval string.length "Hello"

-- answer here

def sHasLenL : string → ℕ → Prop :=
    λ s n, (string.length s) = n


/-
EXERCISE: Express the property
of natural numbers of being perfect
squares. A number, n, is a perfect
square if there is a number, m, 
such that m * m = n.
-/

