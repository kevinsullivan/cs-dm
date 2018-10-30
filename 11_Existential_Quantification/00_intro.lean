/- ***********************-/
/- *** ∃ Introduction *** -/
/-************************-/

/-
An existentially quantified 
proposition asserts that there
exists *some* value of some type 
that makes a given predicate 
true. Here's an example.
-/

def anExistsProp := 
    ∃ m , m + m = 8

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

A proof of ∃ m , m + m = 8, is
thus the pair, ⟨ 4, eq.refl 8 ⟩. Here we use
special angle brackets, a notation that
Lean recognizes for writing proofs of 
existentially quantified propositions.
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

{ T : Type } { p: T → Prop } (w : T) (e : p w)
---------------------------------------------- exists.intr        
                    ∃ a : T, p a
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

#check existsIntro

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

#reduce fourAgain

/-
Concrete example
-/

def isEven (n : nat) : Prop :=
    exists m : nat, m + m = n

#check isEven

/-
A bad definition of isEven (last time).
-/

def isEvenBadDef (n : nat) : Prop :=
    exists m : nat, n / m = 2

example : isEvenBadDef 7 :=
    ⟨ 3.5, rfl ⟩ 

-- OOPS "/"" is natural number division
#reduce (7 / 2 : nat)

#reduce isEven 8
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


-- Possible Answers --

theorem isNonZ : exists n : nat, 0 ≠ n :=
exists.intro 1 (λ pf : (0 = 1), 
nat.no_confusion pf)
-- second arg is a pf of 0=1→false

theorem isNonZ' : exists n : nat, 0 ≠ n :=
begin
  apply exists.intro 1,
  assume contra: 0=1,
  exact nat.no_confusion contra
end

theorem isNonZ'' : exists n : nat, 0 ≠ n :=
begin
  have pf0isnt1: (0 ≠ 2),
    apply nat.no_confusion,

  exact ⟨ 2, pf0isnt1 ⟩
end

theorem isNonZ''' : exists n : nat, 0 ≠ n :=
  ⟨ 3, dec_trivial ⟩

/- **********************-/
/- *** ∃ Elimination *** -/
/-***********************-/

/-
Suppose you want to show: ∃ x, P x → Q.

If one assumes that ∃ x, P x, then one 
can assume there is some specific value,
w, such that P w is true. If one can then 
show, without making additional assumptions 
about w, that some conclusion, Q (that does
not depend on w), follows, then one has shown
that Q follows from the mere existence of a
w with property P, and thus from ∃ x, P x. 

The formal rule is a little bit involved. 
Here it is as an inference rule. We explain
each piece below.

∀ {Q : Prop}, ∀ {T : Type }, ∀ { P : T → Prop},
pfEx: (∃ x : T, P x), pfP2Q: ∀ w : T, P w → Q
----------------------------------------------
               Q

Ignore the implicit parameters for a moment,
and focus on pfEx and pfP2Q. This rule says 
that (1) if there is some object, x that has
property P, and (2) if whenever *any* object 
has this property, Q follows, then Q follows.

This is the elimination rule for ∃. It 
lets you draw a conclusion, Q, from the
premise that ∃ x, P x (there is an x with
property P) and from a proof that if any 
x has this property (and we just assumed
there is one) then there is a proof of Q.

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

-- assume pred1 and pred2 are properties of nats
variable pred1 : ℕ → Prop
variable pred2 : ℕ → Prop

/-
∀ {Q : Prop}, ∀ {T : Type }, ∀ { P : T → Prop},
pfEx: (∃ x : T, P x), pfP2Q: ∀ w : T, P w → Q
----------------------------------------------
               Q
-/

theorem forgetAProperty : 
  (exists n, pred1 n ∧ pred2 n) → (exists n, pred1 n) :=
-- here "Q", the conclusion, is (exists n, pred1 n)
begin
  assume ex,
  show ∃ (n : ℕ), pred1 n,
  from
    begin
      apply exists.elim ex, -- give one arg, build  other
      assume w Pw,          -- assume w and proof of P w
      show ∃ (n : ℕ), pred1 n,
      from exists.intro w Pw.left,
    end,
end

/-
We'll need to understand the following fact
to fully understand the proof of the theorem
that follows. This fact says that if "a" is a
value (here of type ℕ) and pred is a predicate 
on values (or type ℕ), and if you further have 
a function that takes a value, x, and returns
pred x, then applying that function to a value
a returns pred a. Just keep this in mind as we
work through the follow-on proof.  
-/

example:
  ∀ (a: ℕ), ∀ (pred: ℕ → Prop),
    (λ (x: ℕ), pred x) a = (pred a) :=
begin
  assume a pred,
  apply rfl
end

/-
We now define two simple predicates,
gt1 (λ x, x > 1) and pred4 (λ x, x < 4), 
and two more complex predicates, P and Q.
P is the predicate that asserts that both
gt1 and pred4 are true of some x, and 
Q is the predicate that asserts that 
there is some x that satisfies gt1.

The reason for this "set up" is so that
we can state the main theorem that follows
in a way that makes cler the relevance 
of the elimination rule for exists. We
want to prove Q from ∃(x: ℕ), P x. 
-/

def gt1: ℕ → Prop := λ (x: ℕ), x > 1
def lt4: ℕ → Prop := λ (x: ℕ), x < 4
abbreviation P : ℕ → Prop := λ (x: ℕ), gt1 x ∧ lt4 x
abbreviation Q : Prop := ∃ (x: ℕ), gt1 x

#check P 2

theorem forgetAProperty':
  (∃(x: ℕ), P x) → Q :=
begin
  assume pf_existsP,
  show Q,  -- document goal for readability
  from
    begin
      apply exists.elim pf_existsP, -- give one arg, build  other
      assume w pf_Pw,               -- assume w and proof of P w
      show Q,
      apply exists.intro w,
      exact pf_Pw.left,
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

theorem reverseProperty : ∀ (P S : ℕ → Prop),
  (exists n, P n ∧ S n) → (exists n, S n ∧ P n) :=
  -- here Q, the conclusion, is (exists n, S n ∧ P n)
begin
  assume P S,
  assume ex,
  show ∃ (n : ℕ), S n ∧ P n,
  from
    begin
      apply exists.elim ex, -- give one arg, build other
      assume w Pw,          -- assume w and proof of P w
      show ∃ (n : ℕ), S n ∧ P n,
      -- here's some new notation for and.intro
      from ⟨ w, ⟨ Pw.right, Pw.left ⟩ ⟩
    end,
end

/-
The difficulty of proving propositions in
predicate logic is often related to the
nesting of quantifiers. Here's a little
example illustrating such nesting.

We formalize and prove this claim: if
there is a person who can be fooled at
any time, then at any time someone can
be fooled. 

Here's a logical rendition of this idea:  
∃ p ∈ Person,   ∀ t ∈ Time,     canFool(p, t) → 
∀ t ∈ Time,     ∃ p ∈ Person,   canFool(p, t). 

Note the different nestings of the quantifiers.

Let's prove it.
-/

theorem existsforall_impl_forallexists:
∀ (Time Person: Type),
∀ (canFool: Time → Person → Prop),
    (∃ p: Person, ∀ t: Time, canFool t p) →
        (∀ t: Time, ∃ p: Person, canFool t p)
:=
begin
  assume Time Person,
  assume canFool,
  assume someoneCanBeFooledAllTheTime,
  show ∀ (t : Time), ∃ (p : Person), canFool t p, from
  begin
    assume aTime,
    show ∃ (p : Person), canFool aTime p, from
        begin
        apply exists.elim someoneCanBeFooledAllTheTime,
        assume somePerson,
        assume canFoolThatPersonAnytime,
        have canFoolThatPersonSometime := 
            canFoolThatPersonAnytime aTime,
        exact exists.intro somePerson canFoolThatPersonSometime,
        --exact ⟨ somePerson, canFoolThatPersonSometime ⟩, 
        end,
  end,
end

/-
The same proposition and proof using neutral identifiers.
-/
theorem existsforall_impl_forallexists':
∀ (T P: Type),
∀ (rel: T → P → Prop),
    (∃ p: P, ∀ t: T, rel t p) →
        (∀ t: T, ∃ p: P, rel t p)
:=
begin
  assume T P,
  assume rel,
  assume somePrelAllT,
  assume someT,
  apply exists.elim somePrelAllT,
  assume someP,
  assume thatPrelAllT,
  have thatTrelThatP := 
    thatPrelAllT someT,
  exact ⟨ someP, thatTrelThatP ⟩, 
end

/-
Discussion: Is the converse proposition true?
-/

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
    (¬(∃(t: T), pred(t))) ↔
      ∀(t: T), ¬pred(t) :=
begin
  assume T pred,
  apply iff.intro,

  -- forward
  show (¬∃ (t : T), pred t) → ∀ (t : T), ¬pred t, from
    begin
        assume pf_not_exists_t,
        show ∀ (t : T), ¬pred t, from
        begin
            assume t,
            assume pred_t,
            have pf_exists_t := exists.intro t pred_t,
            exact (pf_not_exists_t pf_exists_t),
            -- contradiction,
        end,
    end,

    -- reverse
  show (∀ (t : T), ¬pred t) → (¬∃ (t : T), pred t), from
    begin
        assume all_not_pred,
        show ¬∃ (t : T), pred t, from
            begin
            assume ex_t_pred,
            show false, from
                begin
                apply exists.elim ex_t_pred,
                assume t,
                assume pred_t,
                have not_pred_t := all_not_pred t,
                --exact pf_not_pred_t pf_pred_t
                contradiction,
                end,
            end,
    end,
end

open classical
-- em is axiom of the excluded middle

theorem not_all_t_iff_exists_not_t:
  ∀ (T: Type) (pred: (T → Prop)),
    (¬(∀ t: T, pred(t))) ↔
      ∃ t: T, ¬pred(t) :=
begin
  intros,
  apply iff.intro,
    assume pf_not_all_t,
    cases (em (∃ (t : T), ¬pred t)) with pf_exists_not_t pf_not_exists_not_t,
      exact pf_exists_not_t,

      have contra_double_neg: ∀(t: T), ¬¬pred t,
        assume t,
        assume pf_n_pred_t,
        have pf_exists_t := exists.intro t pf_n_pred_t,
        exact (pf_not_exists_not_t pf_exists_t),
      
      have contra: ∀(t: T), pred t,
        assume t,
        have pf_nn_pred_t := (contra_double_neg t),
        cases em (pred t) with pf_pred_t pf_n_pred_t,
          assumption,

          exact false.elim (pf_nn_pred_t pf_n_pred_t),
    
      exact false.elim (pf_not_all_t contra),

    assume pf_exists_not_t,
    apply exists.elim pf_exists_not_t,
    assume w not_pred_w,
    assume pf_all_t,
    show false, from
      begin
        have pred_w := pf_all_t w,
        exact not_pred_w pred_w,
      end,
end

/-
Satisfiability

Satisfiability is about finding values for
sub-propositions that make a larger proposition
true. We typically like to formulate these
questions in something known as conjunctive
normal form (or CNF). In CNF we have a series
of disjunctions, e.g., x1 ∨ x2 ∨ ¬x3 ∨ x4.
These disjunctions are then combined into
the larger proposition using conjunctions, e.g.:
(x1 ∨ x2 ∨ ¬x3 ∨ x4) ∧ (¬x1 ∨ x2 ∨ ¬x3).


For example, do there exist values for P and Q
such that:
(P ∨ Q) ∧ (¬P ∨ ¬Q) is true?
-/

example: ∃(P Q: Prop), (P ∨ Q) ∧ (¬P ∨ ¬Q) :=
begin
  apply exists.intro true,
  apply exists.intro false,
  apply and.intro,
    -- prove true or false
    apply or.inl true.intro,

    -- prove not true or not false,
    apply or.inr false.elim,
end

/-
Exercise:
Do there exist values for P and Q such that:
(P ∨ Q) ∧ (¬P ∨ ¬Q) ∧ (¬P or Q) is true?
If so, prove it.
-/




-- Answer:


example: ∃(P Q: Prop), (P ∨ Q) ∧ (¬P ∨ ¬Q) ∧ (¬P ∨ Q) :=
begin
  apply exists.intro false,
  apply exists.intro true,
  apply and.intro,
    -- prove true or false
    apply or.inr true.intro,

    apply and.intro,
      -- prove not true or not false
      apply or.inl false.elim,

      -- prove not false or true
      apply or.inr true.intro
end

/-
Exercise:
Do there exist values for P and Q such that:
(P ∨ Q) ∧ (¬P ∨ ¬Q) ∧ (¬P ∨ Q) ∧ (¬Q) is true?
If so, prove it.
-/




-- Answer:


-- No such values exist


/-
3-SAT

3-SAT is a special case of satisfiability where
there are no more than 3 terms in each disjunction.

The above problems were technically all 3-SAT.

Here is one that uses all 3 terms:

Exercise:
Do there exist values for P, Q, and R such that:
(P ∨ Q ∨ R) ∧ (¬P ∨ ¬Q ∨ ¬R) ∧ (¬P ∨ Q ∨ R) ∧ (¬Q ∨ ¬R) is true?
-/




-- Answer:


example: ∃(P Q R: Prop), 
  (P ∨ Q ∨ R) ∧ (¬P ∨ ¬Q ∨ ¬R) ∧
   (¬P ∨ Q ∨ R) ∧ (¬Q ∨ ¬R) :=
begin
  apply exists.intro false,
  apply exists.intro true,
  apply exists.intro false,
  apply and.intro,
    -- prove false ∨ true ∨ false
    apply or.inr,
    exact or.inl true.intro,

    apply and.intro,
    -- prove ¬false ∨ ¬true ∨ ¬false
    exact or.inl false.elim,

    apply and.intro,
    -- prove ¬false ∨ true ∨ false
    exact or.inl false.elim,

    -- prove ¬true or ¬false
    exact or.inr false.elim
end