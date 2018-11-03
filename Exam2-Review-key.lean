/-
You need to understand the following
elements of automated predicate logic 
for Exam 2

Suppose P and Q are arbitrary propositions 
(i.e., P Q : Prop) and T and V are arbitrary
types (i.e., T V : Type). 

Know the following forms, how to prove them, 
how to use proofs of them, and how to do these 
things in Lean. 

To know how to prove them and how to use proofs
of them, you need an intuitive understanding of
the introduction and elimination rules for each
form, and how to use them in Lean.

* true : Prop
* false : Prop
* =                    -- equality
* P ∧ Q : Prop
* (∀ p : P, Q) : Prop  -- Q can involve p
* T → V : Type         -- function type)
* P → Q : Prop         -- implication)
* ¬ P : Prop
* P ↔ Q : Prop
* P ∨ Q : Prop
* (∃ p : P, Q) : Prop  -- Q can involve p
* T → Prop             -- a property of Ts
* T → V → Prop         -- a T-V binary relation

Knowing this material, you are also expected to be
able to combine these reasoning rules to prove more 
interesting propositions. In general, such a proof
first applies elimination rules to obtain additional 
useful elements from given assumptions, and then uses 
introduction  rules to combine the elements obtained 
into proofs of desired conclusions. 

You should have an intuitive understanding of the
meaning of each form and how to use each form in 
logical reasoning. In particular, understand (1)
the introduction rules for each -- how to construct
proofs in these forms -- and (2) the elimination
rules for each form -- how to use proofs in these 
forms to obtain additional facts to be used in 
constructing proofs of other propositions.

For extra credit, be able to work in Lean with
(1) propositions and proofs involving combinations 
of quantifiers, such as (∀ x : X, ∃ y : Y, Z) and
(∃ x : X, ∀ y : Y, Z), and with (2) negations of 
quantified propositions, such as ¬ (∃ p : P, Q) 
and ¬ (∀ p : P, Q).

The test will be structured to help you to know and
to show how far you've gotten and where you still 
have some work to do. 

Here are exercises for each form.
-/

/- ***************************************** -/
/- ***************** true ****************** -/
/- ***************************************** -/

/- 
(1)

Use "example" in Lean to prove that there
is a proof of true.  Be sure that after the :=
you can provide a proof using both an expression
and a tactic script.
-/

example : true := true.intro

/- ***************************************** -/
/- ***************** false ***************** -/
/- ***************************************** -/

/-
(2)
Use "def" in Lean to define a function, fq, 
that proves that if P and Q are propositions 
and if Q is true then false → ¬ Q.
-/

def fq (P Q : Prop) (q : Q) : false → ¬ Q :=
begin
assume f : false,
apply false.elim f,   -- shorthand false.elim f
end

/-
(3)
Use "example" in Lean to prove that if 0 = 1
then 0 ≠ 1.
-/

example : 0 = 1 → 0 ≠ 1 :=
begin
assume zo,
have f : false := nat.no_confusion zo,
/-
nat.no_confusion applied to an assumed
proof that 0, specifically, is equal to 
something that is not zero, returns a
proof of false. The false elimination
principle then finishes off the proof.
-/
exact false.elim f,
end

/-
(4) Use "example" to prove that for any two
natural numbers, a and b if a = b then if 
b ≠ a then a ≠ b.
-/

example : ∀ a b : ℕ, a = b → b ≠ a → a ≠ b :=
begin
assume a b,
assume aeqb,
assume nbeqa,
/-
The trick in this case is to apply
the symmetry rule for equality to 
the proof of a=b to get a proof of 
b=a so that you have a contradiction
that you can exploit to get a proof
of false, at which point you can use
false elimination.
-/
have beqa := eq.symm aeqb,
contradiction,
-- shorthand for (false.elim (nbeqa beqa))
end


/- ***************************************** -/
/- ***************** and ******************* -/
/- ***************************************** -/

/-
(5) 

Use "example" to prove that if P, Q, and R 
are propositions, P → Q → R → (P ∧ Q) ∧ R
-/

example : 
    ∀ P Q R : Prop, P → Q → R → (P ∧ Q) ∧ R :=
begin
intros P Q R p q r,
exact (and.intro (and.intro p q) r), 
end


/-
(6) 

Use "example" to prove that if P, Q, and R 
are propositions, (P ∧ Q) ∧ R → P ∧ R.
-/

example : 
    ∀ P Q R : Prop, (P ∧ Q) ∧ R → P ∧ R :=
begin
intros P Q R pqr,
exact and.intro pqr.left.left pqr.right,
-- the following shorthand also works
-- exact ⟨ pqr.left.left, pqr.right ⟩ 
end

/- ***************************************** -/
/- *************** functions *************** -/
/- ***************************************** -/

/-
(7) Use example to prove that if S and T 
are arbitrary types and if there is a value, 
t : T, then S → T. Remember that a proof of 
S → T has to be a function that, if given any 
value of type S, returns some value of type T.

Present this proof as a Python-style function
definition, isFun, then using a tactic script. 
The Π you can read and treast as ∀, for now.
-/

def isFun (S T: Type) (t : T) : S → T :=
/-
The key idea captured by this example is
that if you already have a value of type T
"lying around" (which you do in this case),
you can always define a function from S to
T. All it has to do is ignore its argument
and return t.

Similarly, if S and T were propositions, if
you have a proof, t, that T is true, then 
you can easily prove S → T, and you'd do it
in exactly the same way. Assume a proof of
S, ignore it, and just return the proof, t,
of T, that you already have.

So, here's the function.
-/
    λ s, t

-- and as a tactic script
example : ∀ S T : Type, T → (S → T) :=
begin
assume S T,
assume t,
show S → T,
from λ s, t,
end

/-
(8) use def to define comp to be a function 
that takes as its argments, the types S, T, 
and R, along with a function of type S → T 
and a function of type T → R and that returns 
a function of type S → R. It should take S,
T, and R implicitly and st and tr explicitly.
-/

def 
/-
The arguments, S, T, and R are designated as
implicit by enclosing them in curly braces.
The values of these arguments (the types) can
be inferred from the explicit arguments, st 
and tr.
-/
comp {S T R : Type}
(st : S → T) 
(tr: T → R) 
: S → R :=
/-
The comp (short for "compose") function,
given functions st and tr, composes them
into a function that takes an argument of
type S and returns a value of type R, by
first applying st to s, and then applying
tr to the result.
-/
λ s, tr (st s)

/-
(9) Define square to be a function that
takes a natural number and returns its
square, and inc to be a function that
takes a nat, n, and returns n + 1. Now
use def and comp to define incSquare to
be a function that takes a nat, n, as an
argument and that returns one more than
n^2. Use #reduce to check that the value
of (incSquare 5) is 26. 
-/

def square (n : ℕ) := n^2
def inc (n : ℕ) := n + 1
def incSquare := comp square inc
#reduce incSquare 5

/-
(10)

Consider the function, sum4, below. What
is the type of (sum4 3 7)? What function is
(sum4 3 7)? Answer the second question 
with a lambda abstraction.
-/

/-
NOTE: Sorry, when we posted this problem,
we deleted the definition of sum4 by mistake.
Here it is along with the solution.
-/

def sum4 (a b c d : ℕ) := a + b + c + d

#check sum4

#check sum4 7
#reduce (sum4 7)
#reduce (sum4 7 3)
#reduce (sum4 7 3 11)
#reduce (sum4 7 3 11 2)

-- ℕ → ℕ → ℕ → ℕ → ℕ 
-- ℕ → (ℕ → (ℕ → (ℕ → ℕ))

-- The type of sum4 3 7 is ℕ → ℕ → ℕ 

/-
The function, sum 3 7, is the function,
λ a b, 10 + a + b, i.e., the function that
adds 10 to the sum of its two arguments.
-/

/- ***************************************** -/
/- ************** implication ************** -/
/- ***************************************** -/

/-
(11)

Use example to prove (1) false → false, (2)
false → true, (3) ¬ (true → false).
-/

example : false → false := λ f : false, f

example : false → true := λ f, true.intro

example : ¬ true → false :=
begin
assume tf : true → false,
have t : true := true.intro,
contradiction,
end


/-
pf : ∃ n : ℕ, P n
-/


/-
(12) NOTE CORRECTION HERE!!

Use example to prove that for any two 
propositions, P, Q, if P ∧ Q is true
then if ¬ (P ∨ Q) is true, then you 
can derive a proof of false.
-/

example : 
∀ P : Prop, ∀ Q : Prop, 
(P ∧ Q) → ¬ (P ∨ Q) → false :=
begin
intro P,
intro Q,
assume paq,
intro npaq,
have p := paq.left,
have porq := or.intro_left Q p,
--apply false.elim (npaq porq),
contradiction,
end

/-
The contradiction tactic looks for two
contradictory assumptions in the context,
and if it finds them, applies false.elim
automatically.
-/
example : 
∀ P Q : Prop, 
P ∧ Q → ¬ (P ∧ Q) → false :=
begin
intros, -- let Lean give names to assumptions
contradiction,
end


/- ***************************************** -/
/- *************** forall (∀) ************** -/
/- ***************************************** -/

/-
(13) 

Use example to prove that for all proposition,
P, Q, and R, if P → Q → R then P → R.
-/

/-
You might have been tempted to prove this, but
it's the wrong proposition.
-/

example : ∀ P Q R : Prop, P → Q → R → (P → R) :=
begin
intros P Q R,
intros p q r,
exact λ p, r
end

/-
As written in English, the proposition to be
proved the following, and it can't be proved 
because it isn't true in general.
-/

example : ∀ P Q R : Prop, (P → Q → R) → (P → R) :=
begin
intros P Q R pqr,
assume p,
have qr := pqr p,
-- need but don't have a proof of Q
-- so we can only abandon the proof
end

/-
(14)

Prove that for any type, T, for any a : T, 
and for any property, (P : T → Prop), if 
(∀ t : T, P t), then P a.
-/

example : ∀ T : Type,  ∀ a : T, 
    ∀ (P : T → Prop), (∀ (t : T), P t) → P a := 
begin
assume T a P f, 
exact f a
end

/-
This example illustrates the principle of 
∀ elimination. A ∀ is really just a function
in constructive logic, expressing the idea 
that if you provide *any* value of some type,
then there is a value of another type, namely
a proof of the following proposition. If you
have such a function, and a value of type T,
then you can obtain a proof of P a by simply
applying the "function" to a.
-/


/- ***************************************** -/
/- *************** negation **************** -/
/- ***************************************** -/

/-
(15) 

Show that for any propositions, P and Q, 
¬ ((P ∧ Q) ∧ ((P ∧ Q) → (¬ Q ∧ P)).
-/

example : forall P Q : Prop, 
    ¬ ((P ∧ Q) ∧ ((P ∧ Q) → (¬ Q ∧ P))) :=
begin
    intros,
    assume pf,
    have pq := pf.left,
    have imp := pf.right,
    have nqp := imp pq,
    have q := pq.right,
    have np := nqp.left,
    contradiction,
end

/-
(16)

Prove that for any propositions, P and R, 
if P → R  and ¬ P → R, then R. You might 
need to use the law of the excluded middle.
-/

open classical
example: ∀ P R : Prop, 
    (P → R) → (¬ P → R) → R :=
begin
assume P R pr npr,
/-
At this point it looks like we don't have
much to work with, but remember that if you
are willing to use classical reasoning with
the law of the excluded middle then for any
proposition, you can always use case analysis
to consider what happens if that proposition
is true, then false respectively. Now take
another look at the context? What if P is
true? What is P is false?
-/
have pornp := em P,
cases pornp with p np,
exact (pr p),
exact (npr np),
end




/- ***************************************** -/
/- ************* bi-implication ************ -/
/- ***************************************** -/

/-
(17)

Prove that for propositions P and Q, 
(P -> Q ∧ Q → P) → (Q ↔ P).
-/

example : ∀ P Q : Prop, ((P → Q) ∧ (Q → P)) → (Q ↔ P) :=
begin
assume P Q pf,
exact iff.intro pf.2 pf.1,
end


/-
(18)

Prove that for propositions P and Q,
((P ↔ Q) ∧ P) → Q.
-/

example : forall P Q : Prop,
((P ↔ Q) ∧ P) → Q :=
begin
assume P Q pf,
have bi := pf.left,
have p := pf.right,
have pq := bi.1,
exact pq p,
end

/- ***************************************** -/
/- ************** disjunction ************** -/
/- ***************************************** -/

/-
(19)

Prove that if you eat donuts or if you eat
candy you will get cavities. The proposition
you prove should build in the assumptions 
that if you eat donuts you will get cavities
and if you eat candy you will get cavities. 
We start the proof for you. You complete it.
Start your proof like this:

example : ∀ donut candy cavity : Prop, ...
-/

/-
The problem asks you to prove "you will get
cavities" from a disjunction "eat donuts ∨ 
eat candy." It also allows you to assume
that eating either one will give you cavities.
This is a clear set-up for or elimination.
You could use or.elim directly, or use case
analysis, which is an indirect way of doing
the same thing.
-/

example : ∀ donut candy cavity : Prop,
donut ∨ candy → (candy → cavity) → (donut → cavity) → cavity :=
begin
intros D C V either candy donut,
cases either with d c,
exact (donut d),
exact (candy c),
end


/-
(20)

Prove that if P and Q are any propositions, and
if you have a proof of ¬(P ∨ Q) then you can
construct a proof of ¬ P.
-/

example : ∀ P Q: Prop, ¬ (P ∨ Q) -> ¬ P :=
begin
assume P, 
intro Q,
assume nporq,
assume p,
have porq := or.intro_left Q p,
contradiction,
end
/-
Study this example carefully. The key insight
is that you have a proof of P and you also 
have a proof of ¬ (P ∨ Q), so if you had a
proof of (P ∨ Q), you could use false elim;
but you can get yourself a proof of (P ∨ Q)
from the assumed proof of P using or intro!
This example makes it clear that you really
do have to think about what you have to work
with (in the context) and what you can do 
with it.
-/

example : ∀ P : Prop, P → P :=
begin
assume P,
assume p,
end

/-
(21)

Show, without using em explicitly, that if
for any proposition, P, P ∨ ¬ P, then for any
proposition, Q, ¬ ¬ Q → Q. The proposition to 
prove is (∀ P : Prop, P ∨ ¬ P) → (∀ Q, ¬¬ Q → Q).
Remember that a proof of (∀ P, S) can be applied
to a value of type P to get a value of type S.
-/

example : (∀ P : Prop, P ∨ ¬ P) → (∀ Q, ¬¬ Q → Q) :=
begin
assume em,
assume Q,
assume nnq,
have qornq := em Q,
cases qornq with q nq,
exact q,
apply false.elim (nnq nq),
end
/-
What you're being asked to do here is to 
prove that double negation elimination is
valid if you can assume that ∀ P : Prop,
P ∨ ¬ P.
-/
example : 
    (∀ P : Prop, P ∨ ¬ P) → (∀ Q, ¬¬ Q → Q) :=
begin
assume em,
assume Q, 
have QorNQ := em Q,
cases QorNQ with q nq,
assume nnq, assumption,
assume nnq, contradiction,
end


/- ***************************************** -/
/- **************** predicates ************* -/
/- ***************************************** -/


/-
(22)

Define notZero(n) to be a predicate on
natural numbers that is true when 0 ≠ n
(and false otherwise). Then prove two facts 
using "example." First, ¬ (notZero 0). When
doing this proof, remember what (notZero 0)
means, and remember what negation means.
Second, prove (notZero 1).
-/


/-
A predicate is conceptually a proposition
with one or more parameter values to be
filled in. We represent a predicate as a
function from parameter values to Prop.
In this case, for any natural number, n,
we reduce it to the proposition that that
zero is unequal to the particular n given
as an argument. 
-/
def notZero (n: ℕ) := 0 ≠ n

example : ¬ notZero 0 := 
begin
-- remember that ¬ X means X → false.
assume nzz,
apply nzz (eq.refl 0),
end

example : notZero 1 :=
begin
assume zeqo,
exact nat.no_confusion zeqo,
end

/-
(23)

Define eqString(s, t) to be a predicate on
values of type string, that is true when
s = t (and not true otherwise). Then prove: 
eqString "Hello Lean" ("Hello " ++ "Lean")
-/

def eqString: string → string → Prop :=
λ s t, s = t

/-
What we have here is a predicate with two
arguments, which defines a binary relation.
Here the relation is one of equality between
pairs of strings. This relation contains all
pairs of strings where the two elements are
equal, and it contains no other pairs. We
can prove that a particular pair is in the
relation by simply using rfl (if the pair
really is in the relation, of course.) This
example shows again that equality in Lean
doesn't require exactly equal terms, but
rather terms that reduce to the same values. 
-/

example : 
eqString "Hello Lean" ("Hello " ++ "Lean") := 
    rfl

/- ***************************************** -/
/- **************** exists ***************** -/
/- ***************************************** -/

/-
(24) 

Prove that ∃ n : ℕ, n = 13. 
-/

/-
A proof of an existentially quantified proposition
in constructive logic is a pair: ⟨ witness, proof ⟩,
where the witness is a value of the right type and
the proof is a proof that that particular witness
has the specified property. Here the only witness
that will work is 13, and the proof that 13 = 13 is
simply by the reflexivity of equality. 
-/

example : ∃ n, n = 13 := exists.intro 13 rfl 


/-
(25)

Prove ∀ s : string, ∃ n, n = string.length s.
-/

/-
This problem just asserts that for any string,
there is a natural number equal to the length 
of the string. And the answer is string.length.
-/

example : 
∀ s : string, ∃ n, n = string.length s :=
begin
intro s,
apply exists.intro (string.length s),
apply rfl,
end


example : 
∀ s : string, ∃ n, n = string.length s :=
begin
assume s,
exact ⟨ string.length s, rfl ⟩ -- exists.intro
end

/-
(26)

Prove exists m : ℕ, exists n: ℕ, m * n = 100.
Remember that you can apply exists.intro to a
witness, leaving the proof to be constructed
interactively.
-/

example : 
    exists m : ℕ, exists n: ℕ, m * n = 100 :=
begin
apply exists.intro 10,
apply exists.intro 10,
exact rfl
end


/-
(27)

Prove that if P and S are properties of 
natural numbers, and if (∃ n : ℕ, P n ∧ S n), then (∃ n : ℕ, P n ∨ S n). 
-/


/-
The proof of this proposition follows the 
common pattern of elmination rules followed 
by introduction rules. Applying the elimination
rule for ∃ (followed by two intros) yields an
assumed witness, n, to (∃ n, P n ∧ S n), and 
a proof, pf, that n has the property of having
both property P and property S. From there it
is a simple matter of using exists intro to
prove the final goal.
-/
example : ∀ P S : ℕ → Prop, 
    (∃ n, P n ∧ S n) → (∃ n, P n ∨ S n) :=
begin
intros P S pfex,
apply exists.elim pfex,
intro w,
assume w_has_prop,
apply exists.intro w,
apply or.intro_left,
exact and.elim_left w_has_prop,
end








assume P S, 
assume ex,
apply exists.elim ex,
assume w pf,
apply exists.intro w,
apply or.inl,
exact pf.left,
end