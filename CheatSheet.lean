/-
This cheat sheet summarizes the 
introduction and elimination
rules for each connective and
quantifier in predicate logic,
used, respectively, to construct
and to take apart, or destruct,
proofs of propositions built 
using these connectives and 
quantifiers. 
-/

/- **** -/
/- true -/
/- **** -/

/-
The proposition, true, has
a single proof and can thus
always be judged to be true. 

The introduction rule gives us
a proof without conditions.

  ---------------- (true.intro)
  true.intro: true

Having a proof of true isn't
very useful. One is always
available, and no information
can be obtained from a proof
of true. We thus don't see a
proof of true very often in
practice.
-/

/- true introduction -/


theorem trueIsTrue : true := 
    true.intro

theorem 
trueIsTrue' : true := 
begin
exact (true.intro),
end


/-*******-/
/- false -/
/-*******-/

/-
The proposition, false, has no
proofs, and can thus be judged 
to be false. Because there is 
no proof of false, there is no
introduction rule for false. On
the other hand, it often happens
in real proofs that one ends up
with inconsistent assumptions, 
which shows that such a case in
reality can't occur. When one
ends up in such a situation, a
proof of false can be derived
from the inconsistency, and the
false elimination rule can then
be used to finish the proof of
the current proof goal.
-/

/- false elimination -/

/-
From an assumed proof of false
(or from a proof of false that
is obtained from a contradiciton), 
any proposition, P, can be proved
by simply applying false.elim to
the proof of false.

  P : Prop, f : false
  ------------------- false.elim
        pf : P
-/

def fromFalse (P: Prop) (f: false) : P :=
    false.elim f

theorem 
fromFalse' : 
∀ P : Prop, false → P := 
λ P f, 
    false.elim f


theorem 
fromFalse'' : 
∀ P : Prop, false → P := 
begin
assume P f,
show P,
from false.elim f,
end


/-**** -/
/- and -/
/-**** -/

/-
If P and Q are propositions, then
P ∧ Q is a proposition. It is read
as asserting that both P and Q are
true. 

To prove P ∧ Q, one applies the 
introduction rule for ∧ to a proof 
of P and to a proof of Q. 

{ P, Q : Prop } (p: P) (q: Q)
----------------------------- and.intro
       ⟨ p, q ⟩ : P ∧ Q

From a proof of P and Q one can derive 
proofs of P and of Q by applying the left
and right elimination rules, respectively.

{ P Q: Prop } (pq : P ∧ Q)
--------------------------- and.elim_left
          p : P


{ P Q: Prop } (pq : P ∧ Q)
--------------------------- and.elim_right
          q : Q
-/

/- and introduction -/

-- P → Q → P ∧ Q

def PandQ (P Q : Prop) (p: P) (q: Q) : P ∧ Q :=
    and.intro p q

#check PandQ

theorem 
PandQ' : ∀ ( P Q : Prop ), P → Q → P ∧ Q  := 
λ P Q p q, 
    ⟨ p, q ⟩ -- shorthand for and.intro p q

#check PandQ'

theorem PandQ'' : ∀ { P Q : Prop }, P → Q → P ∧ Q := 
begin
assume P Q p q,
show P ∧ Q,
from ⟨ p, q ⟩, -- again shorthand for and.intro p q
end

/- and elimination -/

def PfromPandQ (P Q: Prop) (pq: P ∧ Q) : P :=
    and.elim_left pq

def QfromPandQ (P Q: Prop) (pq: P ∧ Q) : Q :=
    and.elim_right pq

theorem PfromPandQ' : ∀ { P Q : Prop }, P ∧ Q → P := 
λ P Q pq, 
    pq.left -- shorthand for and.elim_left pq

theorem QfromPandQ' : ∀ { P Q : Prop }, P ∧ Q → Q := 
λ P Q pq, 
    pq.right -- shorthand for and.elim_left pq

theorem PfromPandQ'' : ∀ { P Q : Prop }, P ∧ Q → P := 
begin
assume P Q pq, 
show P,
from pq.left
end 

theorem QfromPandQ'' : ∀ { P Q : Prop }, P ∧ Q → Q := 
begin
assume P Q pq, 
show Q,
from pq.right
end 


/- ***** -/
/- arrow -/
/-****** -/

/-
If P and Q are propositions, then P → Q
is a proposition. It read as asserting
that if P is true then Q is true. 

To prove P → Q, one must show that there
is a (total) function that, when given a 
proof of P as an argument, constructs a
proof of Q as a result. NB: Functions can
be defined to take argument of types that
have no value! See the false elimination
examples above. It is very important to
understand that P → Q being true does not 
necessarily mean that P is true, but only
that *if* P is true (there is a proof of 
P) then Q is true (a proof of Q can be 
constructed).

To prove P → Q, provide a function that
shows that from an assumed proof of P
one can construct a proof of Q. The type
of such a function is P → Q. 
-/

-- implication introduction

def falseImpliesTrue (f : false) : true :=
    true.intro

#check falseImpliesTrue

example : false → true :=
    λ f : false, true.intro

/- → implication elimination -/

/-
From a proof of P → Q and a proof of P 
one can derive a proof of Q. This is done
by "applying" the proof of the implication
(which in Lean is a function) to the proof
of P, the result of which is a proof of Q.

(P Q : Prop) (p2q: P → Q) (p : P)
--------------------------------- → elim
         (p2q p) : Q
-/

def arrowElim {P Q : Prop} (p2q: P → Q) (p : P) : Q :=
    p2q p 

theorem arrowElim': ∀ { P Q : Prop}, (P → Q) → P → Q :=
λ P Q p2q p, 
    p2q p

theorem arrowElim'': ∀ { P Q : Prop}, (P → Q) → P → Q :=
begin
assume P Q p2q p,
show Q,
from p2q p
end


/- ********** -/
/- forall (∀) -/
/- ********** -/

/-
If P is a type and Q is a predicate,
then ∀ p : P, Q is a proposition. It
is read as stating that the predicate,
Q, is true for any value, p, in the 
set of values (domain of discourse)
given by the type, P. The predicate,
Q, is usually one that takes a value
of type, P, as an argument, but this
is not always the case. For example,
one could write, ∀ n : ℕ, true. Here
the predicate, true, is a predicate
that takes no arguments at all, and
so it is simply a proposition, and it
is true for every value of n, so the 
proposition, ∀ n : ℕ, true, is true.
More commonly, the predicate part of
a universally quantified proposition
will be "about" the values over which
the quantification ranges. Here is an
example: 

∀ n : ℕ : (n > 2 ∧ prime n) → odd n

This proposition asserts that any n
greater than 2 and prime is also odd
(which also happens to be true). The
predicate, (n > 2 ∧ prime n) → odd n,
in this case takes n as an argument,
and is thus "about" each of the values
over which the ∀ ranges.
-/

/- ∀ introduction -/

/-
To prove a proposition, ∀ p : P, Q, 
assume an arbitrary value, p : P,
and shows that the predicate, Q, is
true for that assumed value. As the
value was chosen arbitarily, it thus
follows that the predicate is true
for *any* such value, proving the ∀.  

To see this principle in action, 
study the following proof script.
-/

theorem allNEqualSelf: ∀ n : ℕ, n = n :=
begin
assume n, -- assume an arbitrary n
show n = n, -- show predicate true for n
from rfl, -- thus proving ∀ n, n = n
end

/- ∀ elimination -/

/-
∀ elimination reasons that if some
predicate, Q, is true for every value of 
some type, then it must also be true for 
any particular value of that type. So 
from a proof, p2q, of ∀ P, Q and a proof,
p : P, we conclude Q. 

P : Type, Q : P → Prop, p2q : ∀ p : P, Q, p : P
-----------------------------------------------
            (p2q p) :  Q p

Forall elimination is just another form 
of arrow elimination. In constructive 
logic this is function application. Study 
the following examples carefully to see 
how this works.
-/

def forallElim (p2q: ∀ n : nat, n = n) (p : nat) : p = p :=
    p2q p

def forallElim' (p2q: ∀ n : nat, n = n) (p : nat) : p = p :=
begin
exact (p2q p)
end

#reduce forallElim allNEqualSelf 7



/-***********************-/
/- Negation introduction -/
/-***********************-/

/-
If P is a proposition, then ¬ P is one, too.
We read ¬ P as asserting that P is false. In
constructive logic this means that there is
no proof of P. In constructive logic, ¬ P is
thus actually defined as P → false. So ¬ P
means P → false, and a proof of ¬ P is just
a proof of P → false. 


To prove ¬ P, one thus assumes a proof of P
and shows that in that context one can produce
a proof of false. To this one, one produces a function that takes a proof of P as an argument
and uses it to construct and return a proof of
false. This is the introduction rule for ¬. 
Another way to say this: To prove ¬ P, assume
P and show that this leads to a contradiction.
This is of course just the principle of proof
by negation. 

P: Prop, f2p : false → P
------------------------ false introduction
        np : ¬ P

The elimination rule allows one to reason from
a contradition (a proof of false) to conclude
that any proposition is true. 

P : Prop, f : false
------------------- false.elim
      p : P
-/


-- negation introduction 

def notIntro' (P : Prop) (p2f: P → false) : ¬P :=
    p2f -- a proof of P → false is a proof of ¬ P

theorem 
notIntro : ∀ P : Prop, (P → false) → ¬ P :=
begin
assume P : Prop,
assume p2f : P → false,
show ¬ P,
from p2f
end

/- 
Example: from the assumption that a proposition, P, is true, we can deduce that ¬ ¬ P is true, as
well. 
-/

theorem doubleNegIntro : ∀ P : Prop, P → ¬ ¬ P :=
begin
assume P : Prop,
assume p : P,
assume np : ¬ P, -- ¬ ¬ P means ¬ P → false, so assume ¬ P
show false,
from np p
end

theorem doubleNegIntro' : ∀ P : Prop, P → ¬ ¬ P :=
    λ P p np, 
        np p



/- negation elimination -/

/-
The rule for negation elimination in
natural deduction is really a rule 
for double negation elimination: it
states that, ∀ P : Prop, ¬ ¬ P → P. 

This rule is not valid in constructive 
logic. You can't prove the following 
unless you also accept the axiom of 
the excluded middle, or equivalent.

theorem doubleNegationElim : 
    ∀ P : Prop, ¬ ¬ P → P :=
        -- we're stuck! 

However, if we accept the axiom of the 
excluded middle, which we can do by 
"opening" Lean's "classical" module, 
then we can prove that double negation 
elimination is valid. 
-/

open classical

#check em

/-
Now em is the axiom of the excluded middle.
What em tells us is that if P is any
proposition, then either one of P or ¬ P is 
true, and there are no other possibilities. 

And from em we can now prove double negation 
elimination.  The proof is by "case analysis." 
We consider each of the two possible cases for 
P (true and false) in turn. 

If we assume P is true, then we are done, 
as our goal is to show P (from ¬ ¬ P). On 
the other hand, if we assume P is false, 
i.e., ¬ P, then we reach a contradiction.
We have already assumed ¬ ¬ P is true and
we are trying to prove P. But now if we
also assume that ¬ P is true, then clearly
we have a contradition (between ¬ P and 
¬ ¬ P). Using false elimination finishes
this case leaving us with the conclusion
that P is true in either case.
-/

theorem 
doubleNegationElim : 
∀ P : Prop, ¬ ¬ P → P 
:=
begin
assume P nnp,
show P,
from 
    begin
        -- proof by case analysis for P
        cases em P, -- here we rely on em
        -- case with P is assumed to be true
        exact h,
        -- case with P is assumed to be false
        exact false.elim (nnp h)
        -- em says there are no other cases
    end,
end 

/-
Double negation elimination is the fundamental
operation needed in a proof by contradiction. 
In a proof by contradiction, on tries to prove
P by assuming ¬ P and showing that that leads
to a contradiction, thus to a proof that ¬ P
is not true, that is, ¬ (¬ P). The negation
elimination rule lets us then conclude P. 
-/

/-
Note: The law of the excluded middle
allows you to conlude P ∨ ¬ P "for free," 
without giving a proof of either P or of
¬ P. It is in this precise sense that em
is not "constructive." When using em, you
do not build a "bigger" proof (of P ∨ ¬ P)
from one or more "smaller" proofs (of P or 
of ¬ P). Whereas constructive proofs are
"informative," in that they contain the
smaller proofs needed to justify a given
conclusion, classical proofs are not, in
general. Accepting that P ∨ ¬ P by using
em gives you a proof but such a proof does 
not tell you anything at all about which
case is true, whereas a constructive proof
does.
-/





/- *************** -/
/- bi-implication  -/
/- *************** -/

/-
If P and Q are propositions then so is P ↔ Q.
We read P ↔ Q as asserting P → Q ∧ Q → P. To
prove P ↔ Q, we have to provide proofs of both
conjunctions, and from a proof of P ↔ Q we can
obtain proofs of P → Q and of Q → P by use of
the elimination rule for ↔.

The ↔ symbol is pronounced as is equivalent 
to," or as "if and only if," In mathematical 
writing it is often written as "iff". And to 
get the ↔ symbol in Lean, use backslash-iff.

Its introduction and elimination rules are 
equivalent to those for conjunction, but 
specialized to the case where each of the 
conjuncts is an implication and where one 
is the other going in the other direction.
-/

/- iff introduction -/

/-
To prove P ↔ Q (introduction), apply iff.intro
to proofs of P and Q. 

(P Q : Prop), (pq : P → Q) (qp : Q → P)
--------------------------------------- iff.intro
        pqEquiv: P ↔ Q
    -/

theorem 
iffIntro : ∀ P Q : Prop, (P → Q) → (Q → P) → (P ↔ Q) :=
begin
assume P Q : Prop,
assume p2q q2p,
apply iff.intro p2q q2p
end

theorem 
iffIntro' : ∀ P Q : Prop, (P → Q) → (Q → P) → (P ↔ Q) :=
λ P Q pq qp, 
    iff.intro pq qp


/- iff elimination -/

/-
Similarly, the left and right iff elimination 
rules are equivalent to the and elimination 
rules but for the special case where the 
conjunction is a bi-implication in particular.
-/

theorem
iffElimLeft : ∀ P Q : Prop, (P ↔ Q) → P → Q :=
begin
assume P Q : Prop,
assume bi : P ↔ Q,
show P → Q,
from iff.elim_left bi -- bi.1 is a shorthand
end


theorem
iffElimLeft' : ∀ P Q : Prop, (P ↔ Q) → P → Q :=
λ P Q bi, 
    iff.elim_left bi


theorem
iffElimRight : ∀ P Q : Prop, (P ↔ Q) → Q → P :=
λ P Q bi, 
    iff.elim_right bi


/- **************** -/
/- or (disjunction) -/
/- **************** -/

/-
If P and Q are propositions, then so is P ∨ Q.
P ∨ Q asserts that at least one of P, Q is true,
but it does not indicate which case holds.
-/

/- introduction rules for or -/

/-
To prove P ∨ Q, in constructive logic
one either applies the or.intro_left rule
to a proof of P or the or.intro_right rule
to a proof of Q. In either case, one must
also provide, as the first argument, the
proposition that is not being proved. The
shorthand or.inl and or.inr rules infer
these propositional arguments and are
easier and clearer to use in practice.
-/

theorem orIntroLeft (P Q : Prop) (p : P) : P ∨ Q :=
    or.intro_left Q p -- args: proposition Q, proof of P

theorem 
orIntroLeft': forall P Q: Prop, P → (P ∨ Q) :=
λ P Q p, 
    or.inl p -- shorthand

theorem orIntroRight: forall P Q: Prop, Q → (P ∨ Q) :=
λ P Q q, 
    or.inr q


/- or elimination -/

/-
The elimination rule for or says that if
(1) P ∨ Q is true, (2) P → R, and (3) Q → R,
then you can conclude R. 

The reasoning in by "case analysis." In
one case, if P ∨ Q because P is, then use 
P → R to prove R. Otherwise, if P ∨ Q is 
true because Q is, then use Q → R to prove
R. Usually you don't know which case holds
so to prove R from P ∨ Q you have to show
that R follows "in either case", and to 
do that, you need both P → R and Q → R.

pfPQ: P ∨ Q, pfPR: P → R, pfQR: Q → R
-------------------------------------- or.elim
                 R
                 
So, for example if (1) "it's raining or the 
fire hydrant is running" (P ∨ Q), (2)"if it's 
raining then the streets are wet", and (3)  
"if the fire hydrant is running then the 
streets are wet", then the streets are wet!
-/

theorem orElim : 
forall P Q R: Prop, 
    (P ∨ Q) → (P → R) → (Q → R) → R 
:=
begin
assume P Q R,
assume PorQ: (P ∨ Q),
assume pr: (P → R),
assume qr: (Q → R),
show R,
from or.elim PorQ pr qr 
end

theorem orElim' : 
forall P Q R: Prop, 
    (P ∨ Q) → (P → R) → (Q → R) → R 
:=
begin
assume P Q R,
assume PorQ: (P ∨ Q),
assume pr: (P → R),
assume qr: (Q → R),
show R,
from 
    -- compare carefully with previous example
    begin
    cases PorQ with p q,
    exact (pr p),
    exact (qr q)
    end  
end


-- Same proof, different identifiers
theorem orElimExample' : 
forall Rain Hydrant Wet: Prop, 
    (Rain ∨ Hydrant) → -- raining or hydrant on;
    (Rain → Wet) →     -- if raining then wet;
    (Hydrant → Wet) →  -- if hydrant on then wet;
    Wet                -- then wet
:=
begin
-- setup
assume Rain Hydrant Wet,
assume RainingOrHydrantRunning: (Rain ∨ Hydrant),
assume RainMakesWet: (Rain → Wet),
assume HydrantMakesWet: (Hydrant → Wet),
-- the core of the proof
cases RainingOrHydrantRunning with raining running,
show Wet, from RainMakesWet raining,
show Wet, from HydrantMakesWet running,

end

/-
Note: The axiom of the excluded middle allows
us to do case analysis even if we don't have an
explicit disjunction to work with, because we
can always apply em to any proposition P to get
a proof of P ∨ ¬ P.

Here's an example. (There is a more direct
proof, but we're showing how to apply em to a
proposition to get a disjunction to do case
analysis on.
-/
open classical
example : ∀ P : Prop, P ∨ ¬ P :=
begin
assume P : Prop,
cases (em P) with p np, --(em P) is a proof of P ∨ ¬ P
exact or.inl p,         -- case where P assumed true
exact or.inr np,        -- case where ¬ P assumed true
end

/-
Go back and without fail see where
this trick was used to prove one of
the DeMorgan laws and the validity of
double negation elimination.
-/

/- ********** -/
/- Predicates -/
/- ********** -/

/-
A predicate is a proposition with parameters
whose values need to be supplied to reduce the
predicate to a proposition.

For example, even (n : ℕ) : Prop, could be 
a predicate that takes a value, n : ℕ, and
that reduces to a proposition that in general
will assert something about the particular n
that was supplied as an argument.

So, even 3, for example would reduce to the
proposition that we would interpret as "three
is even", while "even 7" would be (reduce to)
a proposition that 7 is even. 

We formalize predicates as functions that
take arguments and that return propositions
about those arguments. If this is unclear,
re-read the preceding paragraph.

A predicate thus generates a whole family
of propositions, one for each combination 
of values of its arguments. The "even n"
predicate, for example, gives rise to a
whole family of propositions, one for each
ℕ value of n.

Note that you can think of a predicate with
no parameters as just a proposition. 

A predicate with one parameter can be read
as defining a "property" of the values of
its argument type. A sensibly defined even n
predicate, for example, will generate a
proposition that is true for every even
natural number and that is false for every
odd natural number. 

Such a predicate can also be understood to 
define a set, namely the set of all values
for which the corresponding propositions are
true.

A predicate with multiple parameters can
be read as defining a property of, and thus
a set of, ordered pairs (for two arguments)
or more generally tuples of arguments. We
call a set of pairs (or tuples) a relation.

As an example, a predicate "lessThan m n"
could be defined to reduce to a proposition
that is true whenever m is less than n and
that is false otherwise. This predicate 
implictly "picks out" the set of (m, n)
pairs where m is less than n and exlcudes
all pairs where m is not less than n. The
pair (3, 4) is in the lessThan relation in
that the proposition, lessThan 3 4, would 
be true, while (4, 3) would not be in the
relation, in that "lessThan 4 3" would not
be a true/provable proposition.

We formalize predicates as functions from
argument values to propositions. Here are 
some examples.
-/

/-
First, we define zEqz as a predicate
with no arguments. That is to say, it
is just a plain old proposition. No
more need be said.
-/
def zEqz : Prop := 0 = 0

/-
Next, we generalize by making one of
the zero values into a parameter. The
predicate, when provided with a value
for n, reduces to the proposition that
that zero is equal to that particular
n. -/

def nEqz (n : ℕ) : Prop := 0 = n


/-
Note that we could have written this 
definition using a lambda abstraction. 
A benefit is that this way of writing
the same thing makes the nature of 
zEqz'clear by expressing its type 
explicitly: ℕ → Prop.
-/
def nEqz' : ℕ → Prop := λ n, 0 = n

/-
The only value of n that satisfies this
predicate, in the sense that it makes the
corresponding proposition true, is n = 0.
This predicate thus implicitly represents
the set, { 0 }. 
-/

/-
We can further generalize this predicate
by making both values to be compared into
arguments.
-/


/- ******* -/
/- Exists  -/
/- ******* -/

/-
If P is a type and Q is a predicate, 
then ∃ p : P, Q is a proposition. It 
asserts that there is some value, 
p : P, that makes the predicate, Q, 
true.
-/

/- ∃ introduction -/

/-
To prove a proposition of the form,
∃ p : P, Q, one must provide two things:
(1) a specific value, w : P, that we
often call a "witness", and a proof that 
Q is true for that specific w.

So, for example, to prove that there
exists an object, o, that is a cat, it
would suffice to exhibit some object
(the witness), let's call it Nifty, and
a proof, pf, of the proposition, Nifty
is a cat. Then the pair, ⟨ nifty, pf ⟩ 
would be a proof of ∃ o: Object, Cat o. 

The proposition, ∃ o: Object, Cat o, does 
not refer to Nifty or any other object in 
particular. It just asserts that *some*
object out there is a cat. To prove it,
though, you do need to exhibit a specific
object and give a proof that that object
is a cat. You can then conclude that there
is some object that is a cat.

Here's the exists.intro rule, after which 
we give some very simple examples of how it
would be used in code.

(T : Type), (P : T → Prop), (t : T), (pf: P t)
---------------------------------------------- exists.intro
          ⟨ t, pf ⟩ : exists t : T, P t
-/

#check exists.intro

theorem existsIntro :
∀ T : Type,     -- suppose T is a type
∀ P : T → Prop, -- suppose P is a property of values of type T
/-
now if for any t : T, we can show that t has propery P,
then we can construct a proof that *there exists* an x : T 
with property P
-/
∀ (t : T), (P t) → ∃ x : T, P x
:=
begin
assume T: Type,         -- assume T is some type
assume P: T → Prop,     -- and P is a property
-- show that if there's a t with property P (P t), the ∃ is true
show ∀ (t : T), P t → (∃ (x : T), P x), from
    begin
    assume t : T,           -- assume t is some object of type T
    assume pf : P t,        -- and that t has property P
    show ∃ x, P x, from     -- now we can show ∃ x, P x
        (exists.intro t pf) -- using exists.intro
    --  ⟨ t, pf ⟩  would be a shorthand for (exists.intro t pf)
    end,
end


/- existential elimination -/

/-
The reasoning about existential elimination goes
like this. If we know that (∃ x : T, P x), that
there is some value, x of type T with property P, 
then we can temporarily assume that there is some 
specific value, that we will call it by an otherwise 
unused name, u, where u has property P, which is to
say that we also have a proof of (P u).

If the meaning of "a proof of (P u)" doesn't make
sense, go back and review the class material on 
predicates. P is a predicate, i.e., a function 
from T to Prop, u is the name we've given to some
value of type T with property P such that u has
property P, which is to say there is a proof of 
the proposition, (P u).

Now, if from u and a proof of (P u) we can 
construct a proof of some proposition S (a
proposition that does not involve u in any
way), then we can conclude that S follows from
the mere existence of such a u, i.e., from the
truth of ∃ x : T, P x.  

Here is slightly simplified version of the 
exists.elim rule.

{T : Type}, {P : T → Prop}, {Q : Prop}, (ex: ∃ x : T, P x) (p2q: ∀ t : T, P t → Q)
---------------------------------------------------------------------------------- ∃.intro
                                    q : Q

Let's unpack this. The assumptions are that T 
is any type and P is any property of values of
that type. Q is the proposition that we want to
prove follows from ∃ x : T, P x. The additional
fact that is needed to conclude that Q is true
is a proo, p2q, f that if any t : T has property 
P, then Q follows. If we combine this fact, p2q,
with the fact, ex, that there exists such a t,
then we can conclude that Q must be true.
-/

#check exists.elim

/-
Here's some code that illustrates the use of 
the exists.elim principle in Lean.
-/

def existElimExample
(T : Type)                      -- Suppose T is any type
(P S : T → Prop)                -- and P, S are properties of T
(ex : exists x, P x ∧ S x)      -- and there is an x with P and S
: (exists y, S y ∧ P y)         -- show there is a y with P
:=
begin
/-
The only thing we have to work with is ex. So we will 
apply exists.elim to it. We supply the first argument,
namely the proof of exists x, P x ∧ Q x-/
apply exists.elim ex,
/-
What we then have to provide is the proof required as
the second argument to exists.elim. This is a proof of
the proposition that that for any object, a : T, if a
has properties P and S, then (∃ (y : T), S y ∧ P y) is
true. We will now prove this proposition to finish off
the proof. What we have to prove is an implication, so
we will start by assuming its premises: that a is some 
value of type T and that we have a proof that a has the
properties P and S.
-/
assume a : T,
assume pfa : P a ∧ S a,

/- 
Given these assumption we now need to show the final
conclusion, that (∃ (y : T), S y ∧ P y). This is a job
for exists.intro. The arguments we will give it are 
a as a witness, and of (S a ∧ P a) that we can now
construct from the assumed proof of (P a and S a). 
-/
    show (∃ (y : T), S y ∧ P y), from
    begin
        have pa := pfa.left,
        have qa := pfa.right,
        have qp := and.intro qa pa,
        exact exists.intro a qp
    end
end