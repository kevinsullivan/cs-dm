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


/- ***************************************** -/
/- *************** functions *************** -/
/- ***************************************** -/

/-
(7) Use example to prove that if S and T 
are arbitrary types and if there is a value, 
t : T, then S → T. Remember that a proof of 
S → T has to be a function that if given any 
value of type S returns some value of type T.

Present this proof as a Python-style function
definition, isFun, then using a tactic script. 
The Π you can read and treast as ∀, for now.
-/

def isFun (S T: Type) (t : T) : S → T :=
    λ s, t

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
comp {S T R : Type}
(st : S → T) 
(tr: T → R) 
: S → R :=
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

def sum4 (a b c d : ℕ) := a + b + c + d

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
(12)

Use example to prove that for any two 
propositions, P, Q, if P ∧ Q is true
then if ¬ (P ∨ Q) is true, then you 
can derive a proof of false.
-/

example : 
∀ P Q : Prop, 
P ∧ Q → ¬ (P ∧ Q) → false :=
begin
intros P Q paq npaq,
exact (npaq paq),
end


/- ***************************************** -/
/- *************** forall (∀) ************** -/
/- ***************************************** -/

/-
(13) 

Use example to prove that for all proposition,
P, Q, and R, if P → Q → R then P → R.
-/

example : ∀ P Q R : Prop, P → Q → R → (P → R) :=
begin
intros P Q R,
intros p q r,
exact λ p, r
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
cases (em P) with p np,
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
assume P Q npq,
assume p,
have pq := or.intro_left Q p,
contradiction,
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

def notZero (n: ℕ) := 0 ≠ n

example : ¬ notZero 0 := 
begin
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

example : ∃ n, n = 13 := exists.intro 13 rfl 


/-
(25)

Prove ∀ s : string, ∃ n, n = string.length s.
-/

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

example : ∀ P S : ℕ → Prop, 
    (∃ n, P n ∧ S n) → (∃ n, P n ∨ S n) :=
begin
assume P S, 
assume ex,
apply exists.elim ex,
intros n pf,
apply exists.intro n,
exact or.inl pf.left,
end