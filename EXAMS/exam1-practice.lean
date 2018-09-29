/-***************-/
/- ** BASICS ** --/
/-***************-/

/-
# 

Write a defintion of x as a value of 
type nat having the specific value 0.
Be sure it type-checks. 
-/


/-
# 

Write a definition of f as a function
of type ℕ → ℕ that returns the square of
the value to which it is applied (i.e.,
that it is given as an argument)
-/


/-
#

Write a definition of a function, nt, that
takes any proposition, P, and that returns
the proposition, P → false. 
-/


/-
#

What is the type of this function? Hint:
Use #check to check it.
-/


/-****************************************-/
/- ** PROOFS OF EQUALITY PROPOSITIONS ** --/
/-****************************************-/


/-
#1 

Write a function that takes any type, 
T : Type, and any value, t : T, and that 
returns a proof of t = t.
-/



/-
#2a

Write a function that takes any type, T; three values, 
a, b, and c, of type T; a proof of a = b; and a proof 
of b = c; and that returns a proof of c = a. We give
you most of the answer. Replace the sorry with your
answer.  
-/

def aBbCCa 
    { T : Type } 
    (a b c : T)
    (ab : a = b)
    (bc: c = b) :
    (c = a) 
    := sorry


/-
#2b.

Define aBbCCa' to be the same function, but specify 
its type using ∀ and → connectives, and then provide
the function value using a lambda expression (λ). So
you will start with "def", then the name, then a :,
then the proposition, starting with ∀ and ending with
→ (c = a), followed by :=, and finally follwed by a
lambda expression.
-/

-- your answer here 


/-*******************************-/
/- ** PROOFS OF CONJUNCTIONS ** --/
/-*******************************-/

/-
We assume P Q and R are propositions using the
following "variables" declaration. That means that
we can use P, Q, R, and S in the following theorems
without having to use ∀ P Q R S : Prop to introduce
them again for each individual proposition.
-/

variables P Q R S : Prop

/-
Prove the following propositions by completing
the definitions (replace sorrys with your answers).
-/

theorem t1 : P → Q → R → P := sorry

theorem t2 : Q → (Q ∧ Q) := sorry 

theorem t3 : (P ∧ Q) ∧ (Q ∧ R) → (P ∧ R) := sorry



/-*******************************-/
/- ** PROOFS OF IMPLICATIONS ** --/
/-*******************************-/

/-
Prove the following theorem. It claims that
implication is transitive (which it is).
-/

theorem t4 : ((P → Q) ∧ P) → Q := sorry

theorem t5 : 
    (P → Q) → (Q → R) → (R → S) → (P → S) := sorry
        

/-******************-/
/- ** Functions ** --/
/-******************-/


/-
Complete the following definition
with a value that makes the definition
type-check. You can answer with a
lambda expression. You can also
use a tactic script if you prefer.
-/
def n2n : ℕ → ℕ := 
    sorry

/-
Define a function called double 
that takes any natural number, n, 
and returns two times n. 
-/

-- Your answer goes here



/-
Write a test case for double
in the form of a theorem called
d15is30, that asserts that the
double of 15 is 30, and prove it.
-/

--- Your answer here

/-
Write a function, sum3, that takes three 
natural numbers, a, b, c, and that returns
the sum of a, b, and c. Use a λ expression
to express the function.
-/

-- Your answer here


/-*****************-/
/- ** NEGATION ** --/
/-*****************-/

/-
You already know that double
negation elimination requires
classical reasoning (using the 
law of the excluded middle).
Give a proof of the following
proposition, which asserts that
it's valid to introduce double
negatations. Note: You do not 
need the law of the excluded
middle to prove it.
-/

def t6 : P → ¬ ¬ P := sorry


/-
You've learned a few important 
proof strategies. Explain in a 
few words when might a proof
by negation be attempted, and 
how one proceeds to use it.

Know the answer to the same
question about a proof by
contradiction. 
-/

/-
Explain precisely why using a
proof by contradiction relies
on classical reasoning using
the law of the excluded middle.
-/

/-
EXTRA CREDIT: Write a function 
that takes a function, f, of type
ℕ → ℕ, and that returns a function
that, for any value, n, returns 
one more that what f returns. 
-/

/-
That's the end of the practice test.
Here's a partial inventory of inference
rules we've covered. and related concepts.
This is not enough material for a complete
review. Reread all the notes and work any
problems that you're not yet sure you know
how to solve.
-/


/-
Partial inventory of inference rules.

* Equality
-- eq.refl : given a type T and a value t : T, derives a proof of t = t
-- eq.symm : given a type T, values a b : T, and a proof of a = b, derives a proof of b = a
-- eq.trans : given a type T, values a b c : T, and proofs of a = b and b = c, derives a proof of a = c

* Conjunction
-- and.intro : given propositions, P Q : Prop, a proof P : P, and a proof q : Q, derives a proof of P ∧ Q
-- and.elim_right : given propositions, P Q : Prop and a proof pq : P ∧ Q, derives a proof of P
-- and.elim_right : given propositions, P Q : Prop and a proof pq : P ∧ Q, derives a proof of Q

* Implication
-- → introduction: given P Q : Prop and a derivation of a proof Q from a proof of P, conclude P → Q
-- note : a derivation of a proof of Q from a proof of P is given as a function of type P → Q
-- → elimination: given propositions, P and Q, a proof of P → Q, and a proof of P, derive a proof of Q
-- note that → elimination is both a formal version of Aristotle's modus ponens rule and function application

* Negation
-- introduction : given a proposition P and a proof of P → false, conclude ¬ P
-- elimination
---- in constructive logic, showing that a proposition, ¬ P, is false proves only ¬ ¬ P, not that P is true
---- try to derive a proof of P from the assumption of a proof for ¬ ¬ P and you will see the problem
---- you can read ¬ ¬ P as "there's no proof of ¬ P," or as "¬ P is false," 
---- classical logic adds the axiom of the excluded middle (AEM), stating that ∀ P : Prop, P ∨ ¬ P
---- if you accept this axiom and you know that ¬ P is false, then P must be true
---- the AEM enables ¬ elimination
---- given a proposition P and a proof of ¬ P → false (of ¬ ¬ P), derive a proof of P

* Forall
-- introduction : to prove ∀ p : P, Q, where P is a type and Q is a proposition that can involve be written in terms of p, show that Q holds for an any arbitrarily assumed value, p, of type P
-- elimination : given a proof of ∀ p : P, Q, and a specific value x : P, conclude Q 
-/