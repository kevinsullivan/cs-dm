/- ***********************-/
/- *** ∃ Introduction *** -/
/-************************-/

/-
An existentially quantified 
proposition asserts that there
is some value of some type for 
which some proposition involving 
that value is true. Here is an 
example.
-/

def anExistsProp := 
    exists m , m + m = 8

/- This proposition asserts that 
there is some value m (inferred 
to be of type ℕ) that makes the 
sub-proposition, m + m = 8, true. 

Basic algebra tells us that there 
is such a value, namely 4, so this 
proposition can be proved. 

The key thing to remember is that
a proof of such an existentially
quantified proposition is a pair.
The first element is a value that 
makes the sub-proposition true. We
call such a value a "witness". The 
second element is a proof of the 
sub-proposition when the witness
is substituted in. 

So a proof of the proposition, 
exists m , m + m = 8, for example,
will be a pair, where the first
element is the ℕ value 4 and the
second element is a proof of the
proposition that 4 + 4 = 8 (which 
can be produced using rfl).
-/

/-
Here are a couple more examples.
Note, as with all propositions,
these existential propositions do
not have to be true.
-/

def anotherExistsProp := 
  exists m, m > 10

def yetAnotherExistsProp :=
  exists m, m - m = 3

/-
Consider a familiar expression:

You can fool all of the people some of the time…
  ∀ p ∈ People, ∃ t ∈ time, fool(p, t) 
    — everybody can be fooled at one time or another
  ∃ t ∈ time, ∀ p ∈ People, fool(p, t)
    — there exists a time when all of the people can be fooled simultaneously
  ∃ t ∈ time, ∀ p ∈ People, fool(p, t) →
    ∀ p ∈ People, ∃ t ∈ time, fool(p, t)
…and some of the people all of the time.
  ∃ p ∈ People, ∀ t ∈ time, fool(p, t)
    — there exists somebody who can be fooled all of the time
  ∀ t ∈ time, ∃ p ∈ People, fool(p, t)
    — at any given moment, there exists somebody who can be fooled
  ∃ p ∈ People, ∀ t ∈ time, fool(p, t) →
    ∀ t ∈ time, ∃ p ∈ People, fool(p, t)
-/

/-
More generally the introduction 
rule for ∃ is as follows:

(T : Type) (pred: T → Prop) (w : T) (e : p w)
-----------------------------------------------
            ∃ a : T, pred a
-/

#print exists.intro

def existsIntro 
    (T: Type) 
    (pred: T → Prop) 
    (w : T) 
    (e : pred w) 
    : exists w, pred w
    := exists.intro w e

#check existsIntro

/-
Abstract example
-/
variable T : Type
variable witness : T
variable predicate : T → Prop
variable proof : predicate witness

def pf : ∃ m, predicate m := 
    ⟨ witness, proof ⟩ 

def examplePredicate: ℕ → Prop :=
  λ(x: ℕ), x + x = 8

/-
Concrete example
-/

def isEven (n : nat) : Prop :=
    exists m : nat, m + m = n

def eightEven := isEven 8

#check eightEven
#reduce eightEven

lemma pf8is4twice : 4 + 4 = 8 := rfl

-- exact proof term using exists.intro
theorem even8 : eightEven := 
    exists.intro 4 pf8is4twice

-- syntactic sugar
theorem even8' : eightEven := 
    ⟨ 4, pf8is4twice ⟩ 

-- as a tactic script
-- unfold expands a definition
theorem even8'' : isEven 8 := 
begin
  unfold isEven,      -- not necessary
  exact ⟨ 4, pf8is4twice ⟩ 
end 

/-
EXERCISE: Construct a proof, isNonZ,
of the proposition that there exists 
a natural number n such that 0 ≠ n.
-/



-- Possible Answers --

theorem isNonZ : exists n : nat, 0 ≠ n :=
  exists.intro 1 (λ pf : (0 = 1), 
    nat.no_confusion pf)

theorem isNonZ' : exists n : nat, 0 ≠ n :=
begin
  have pf0isnt1: (0 ≠ 1),
    apply nat.no_confusion,

  exact ⟨ 1, pf0isnt1 ⟩
end

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
Assuming n is a natural number and P and S are
properties of natural numbers, prove that
(∃ n, P n ∧ S n) → (∃ n, S n ∧ P n).
-/



-- Answer

theorem reverseProperty : 
  (exists n, P n ∧ S n) → (exists n, S n ∧ P n) :=
  -- here Q, the conclusion, is (exists n, S n ∧ P n)
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
EXERCISE: Express the property, 
of natural numbers, of being a 
perfect square. For example, 9
is a perfect square, because 3
is a natural number such that 
3 * 3 = 9. By contrast, 12 is
not a perfect square, as there 
does not exist a natural number
that squares to 12. 

State and prove the proposition 
that 9 is a perfect square.
-/




-- Answer

def isASquare: ℕ → Prop :=
    λ n, exists m, n = m ^ 2

theorem isPS9 : isASquare 9 :=
begin
  unfold isASquare,
  exact exists.intro 3 (eq.refl 9)
end

/-
Remember this claim:
  ∃ t ∈ time, ∀ p ∈ People, fool(p, t) →
    ∀ p ∈ People, ∃ t ∈ time, fool(p, t)
Let's look at a general proof
-/

theorem existsforall_impl_forallexists:
  ∀ (S T: Type) (pred: (S → T → Prop)),
    (∃ (t: T), ∀ (p: S), pred(p)(t)) →
      (∀ (p: S), ∃ (t: T), pred(p)(t)) :=
begin
  assume S T pred,
  assume existsforall,
  assume p,
  apply exists.elim existsforall,
  assume a pf_forallp_a,
  have pf_a := (pf_forallp_a p),
  exact exists.intro a pf_a,
end

/-
Negating Existential and Universal Quantifiers

What happens when you negate an existential
quantifier? What does this mean:
¬(∃ t ∈ time, fool(me, t)) -
  there does not exist a time when you can fool me
∀ t ∈ time, ¬fool(me, t) -
  at any time, you will not fool me
Are these equivalent?

How about this:
¬(∀ t ∈ time, fool(me, t)) -
  you cannot fool me all of the time
∃ t ∈ time, ¬fool(me, t) -
  there exists a time when you cannot fool me
Are these equivalent?
-/

theorem not_exists_t_iff_always_not_t:
  ∀ (T: Type) (pred: (T → Prop)),
    (¬(∃ t: T, pred(t))) ↔
      ∀ t: T, ¬pred(t) :=
begin
  assume T pred,
  apply iff.intro,
    assume pf_not_exists_t,
    assume t,
    assume Q,
    have pf_exists_t := exists.intro t Q,
    exact (pf_not_exists_t pf_exists_t),

    -- proof that ∀ t: T, ¬pred(t) implies
    -- ¬(∃ t: T, pred(t))
    assume pf_forall_t_not,
    assume pf_not_exists_t,
    apply exists.elim pf_not_exists_t,
    assume a pf_a,
    have pf_not_a := pf_forall_t_not a,
    exact pf_not_a pf_a
end

