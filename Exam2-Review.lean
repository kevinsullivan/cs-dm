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

/- ***************************************** -/
/- ***************** false ***************** -/
/- ***************************************** -/

/-
(2)
Use "def" in Lean to define a function, fq, 
that proves that if P and Q are propositions 
and if Q is true then false → ¬ Q.
-/


/-
(3)
Use "example" in Lean to prove that if 0 = 1
then 0 ≠ 1.
-/


/-
(4) Use "example" to prove that for any two
natural numbers, a and b if a = b then if 
b ≠ a then a ≠ b.
-/



/- ***************************************** -/
/- ***************** and ******************* -/
/- ***************************************** -/

/-
(5) 

Use "example" to prove that if P, Q, and R 
are propositions, P → Q → R → (P ∧ Q) ∧ R
-/



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


/-
(8) use def to define comp to be a function 
that takes as its argments, the types S, T, 
and R, along with a function of type S → T 
and a function of type T → R and that returns 
a function of type S → R. It should take S,
T, and R implicitly and st and tr explicitly.
-/


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


/-
(10)

Consider the function, sum4, below. What
is the type of (sum4 3 7)? What function is
(sum4 3 7)? Answer the second question 
with a lambda abstraction.
-/


/- ***************************************** -/
/- ************** implication ************** -/
/- ***************************************** -/

/-
(11)

Use several "examples" to prove (1) false → false, 
(2) false → true, (3) ¬ (true → false).
-/

/-
(12)

Use example to prove that for any two 
propositions, P, Q, if P ∧ Q is true
then if ¬ (P ∨ Q) is true, then you 
can derive a proof of false.
-/




/- ***************************************** -/
/- *************** forall (∀) ************** -/
/- ***************************************** -/

/-
(13) 

Use example to prove that for all proposition,
P, Q, and R, if P → Q → R then P → R.
-/



/-
(14)

Prove that for any type, T, for any a : T, 
and for any property, (P : T → Prop), if 
(∀ t : T, P t), then P a.
-/




/- ***************************************** -/
/- *************** negation **************** -/
/- ***************************************** -/

/-
(15) 

Show that for any propositions, P and Q, 
¬ ((P ∧ Q) ∧ ((P ∧ Q) → (¬ Q ∧ P)).
-/



/-
(16)

Prove that for any propositions, P and R, 
if P → R  and ¬ P → R, then R. You might 
need to use the law of the excluded middle.
-/




/- ***************************************** -/
/- ************* bi-implication ************ -/
/- ***************************************** -/

/-
(17)

Prove that for any propositions P and Q, 
(P -> Q) ∧ (Q → P) → (P ↔ Q).
-/



/-
(18)

Prove that for propositions P and Q,
((P ↔ Q) ∧ P) → Q.
-/




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
(20)

Prove that if P and Q are any propositions, and
if you have a proof of ¬(P ∨ Q) then you can
construct a proof of ¬ P.
-/



/-
(21)

Show, without using em explicitly, that if
for any proposition, P, P ∨ ¬ P, then for any
proposition, Q, ¬ ¬ Q → Q. The proposition to 
prove is (∀ P : Prop, P ∨ ¬ P) → (∀ Q, ¬¬ Q → Q).
Remember that a proof of (∀ P, S) can be applied
to a value of type P to get a value of type S.
-/



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
(23)

Define eqString(s, t) to be a predicate on
values of type string, that is true when
s = t (and not true otherwise). Then prove: 
eqString "Hello Lean" ("Hello " ++ "Lean")
-/


/- ***************************************** -/
/- **************** exists ***************** -/
/- ***************************************** -/

/-
(24) 

Prove that ∃ n : ℕ, n = 13. 
-/



/-
(25)

Prove ∀ s : string, ∃ n, n = string.length s.
-/


/-
(26)

Prove exists m : ℕ, exists n: ℕ, m * n = 100.
Remember that you can apply exists.intro to a
witness, leaving the proof to be constructed
interactively.
-/



/-
(27)

Prove that if P and S are properties of 
natural numbers, and if (∃ n : ℕ, P n ∧ S n), 
then (∃ n : ℕ, P n ∨ S n). 
-/

