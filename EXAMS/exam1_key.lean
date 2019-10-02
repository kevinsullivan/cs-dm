
/-

POINTS: Welcome to the first CS2102 exam. The exam has 11 questions

and one extra credit question. The first two questions are worth 5

points each. The rest (but for the extra credit) are worth 10 points

each, making a total of 100. The extra credit is worth an addition

5 points. 



ORGANIZATION: The sections of the exam are labelled and organized

around the inference rules we've covered so far: rules for equality,

conjunction, implications, functions, and negations. That said,

there is some mixing of these issues across the sections.



WHAT TO DO: Complete the exam by following the instructions for

each question. Save your file then upload the completed and saved

file to Collab. You have exactly 75 minutes from the start of the

exam to the time where it must be uploaded to Collab.



OPEN NOTES: You may use the class notes for this exam, whether

provided to you by the instructors or taken by you (or for you).



STRICTLY INDIVIDUAL EFFORT: This is a strictly individual exam,

taken under the honor system. Do not communicate with anyone except

for the instructor about the content of this exam, by any means,

until you are absoluately sure that each person you are communicating

with has already completed it.

-/



/-

Write your name and UVa email ID here and acknowledge that you understand

that this exam is an individual exam and that the Honor System is in effect

for this exam (write "I acknowledge it.")



Name: 

Email id:

Acknowledge that the Honor System norms and rules apply:



Now proceed to take the exam!

-/



/- ********************************** -/

/- ** PROOFS INVOLVING EQUALITY ** -/

/- ********************************** -/



/-

#1 - 5 points



Prove that for any type, T, and for any two values, a and b, of type T,

if you assume that there is a proof of a = b (or if you are given such a

proof), then you can derive a proof of b = a. To be precise, what you are to

prove is this: ∀ T : Type, ∀ a b : T, a = b → b = a.



To prove it, you will present a function that, given a type T, two values, a

and b, of type T, and a proof of a = b, returns a proof of b = a.


We give you most of such a function definition, below. Your challenge is to

write the function "body" in place of the sorry. It should be an expression

that evalutes to a proof of b = a. Hint: how do you get a proof of b = a from

a proof, pf, of a = b?

-/



def from_a_eq_b_prove_b_eq_a (T:
Type) (a b : T) (pf : a = b) : b = a
:= eq.symm pf

#check from_a_eq_b_prove_b_eq_a : ∀ (T : Type) (a b : T), a = b → b = a

/-

#2 - 5 points



Here you are asked to prove the same proposition, but now the function type

is writen as, ∀ (T : Type), ∀ (a b : T), a = b → b = a. Give your answer by

replacing the sorry with the required lambda expression.



Hint: A lambda expression is written as lambda followed immediately by the

names of one or more arguments, followed by a comma, followed by the body of

the function that is being defined. 



Hint: the function you are to define has the same arguments in the same order

as the function you defined above!

-/



def from_a_eq_b_prove_b_eq_a' : ∀ (T :
Type), ∀ (a b : T), a = b → b = a :=

λ T a b pf, eq.symm pf







/- ************************************** -/

/- *** PROOFS INVOLVING CONJUNCTIONS *** -/

/- ************************************** -/



/-

For the questions that follow, assume that P, Q, and R are propositions. We

make these assumptions explicit using the following "variables" declaration.

-/



variables P Q R : Prop



/-

#3 - 10 points



Given that we've assumed and defined P, Q, and R are arbitrary propositions,

prove that P → Q → P ∧ Q. Do it by replacing the sorry with either a lambda

expression or a tactic script in the following code.

-/



theorem t1 : P → Q → P ∧ Q :=

λ p q, and.intro p q





theorem t1' : P → Q → P ∧ Q :=

begin

assume p q,

show P ∧ Q,

from and.intro p q

end



/-

#4 - 10 points



Prove that (P ∧ Q) → (Q ∧ P). This implication basically states that

conjunction is commutative. You will prove it by first assuming that you have

a proof of P ∧ Q and by then showing that you can construct a proof of Q ∧ P.

To complete the proof,replace the sorry with either a lambda expression or a

tactic script as you prefer. Hint: remember the introduction and elimination

rules for conjunctions.

-/

theorem t2 : (P ∧ Q) → (Q ∧ P) :=

λ (pf : P ∧ Q), and.intro pf.right pf.left



-- SULLIVAN: Was answer included in distributed exam?





/- ************************************** -/

/- *** PROOFS INVOLVING IMPLICATIONS *** -/

/- ************************************** -/



/-

#5 - 10 points



Prove that (P → Q) → (Q → R) → (P → R). This proposition claims that

implication is transitive (which it is). 



Hint #1: assume that you have a proof of (P → Q). Then assume that you have a

proof of (Q → R). Then, in the context of these two assumptions, show that

you can construct a proof of P → R. 



Hint #2: To prove P → R, assume that you have a proof of P and show that you

can construct a proof of R. 



Hint #3: Proofs of implications can be used to convert proofs of premises

into proofs of conclusions. Think modus ponens.



You can use a lambda expression, tactics, or even a mixture of the two --

whatever you prefer -- to give your answer. 

-/





theorem arrow_trans : (P → Q) → (Q → R) → (P → R) :=

λ pq qr, 

λ p,

qr (pq p)



theorem arrow_trans' : (P → Q) → (Q → R) → (P → R) :=

begin

assume pq qr,

show P → R,

from 

assume p,

show R,

from qr (pq p)

end





/- *************************** -/

/- *** DEFINING FUNCTIONS *** -/

/- *************************** -/





/-

#6 - 10 points



Complete the following definition of a function, square, that takes a natural

number as an argument and that returns the square of that argument as a

result. Give your answer by replacing sorry in the code that follows with

your code.

-/



-- Your answer goes here

def square (n : nat) : nat :=

n * n




/-

#7 - 10 points



Give an alternative implementation of square, here called square', by

replacing the sorry with a lambda expression in the following code.

-/

def square' : ℕ → ℕ :=

λ n, n * n



/-

#8 - 10 points



Write a function, quad, that takes four natural numbers, a, b, c, and x, and

that returns a * x * x + b * x + c. Thus function, quad, is thus to take the

coefficients of a general quadratic function and evaluate it at the value given by x. Use a lambda expression.



Hint, such a function takes four ℕ values as arguments and returns a fifth ℕ

value as a result. Make sure you have the right number of ℕ's when you

declare the type of quad as something like this: def quad : ℕ → ℕ → ...

-/



def quad (a b c x: ℕ) : ℕ :=

a * x^2 + b * x + c

theorem quadRight : quad = λ a b c x, a * x^2 + b * x + c := rfl





/- *********************************** -/

/- *** PROOFS INVOLVING NEGATIONS *** -/

/- *********************************** -/



/-

#9 - 10 points



Given that we've already assumed (above) that Q is some arbitrary (any)

proposition, construct a proof, call it noContra, that (Q ∧ ¬ Q) → false.

Your answer will start like this: theorem noContra : (Q ∧ ¬ Q) → false :=

-/



theorem noContra : (Q ∧ ¬ Q) → false :=

begin

assume contra,

show false,

from contra.right contra.left

end



/-

#10 - 10 points



Construct a proof, call it contraPos, that (P → Q) → (¬ Q → ¬ P).



You can make sense of this proposition using the "rain/wet" example.

If it's true that "if it's raining then the streets are wet" then its

true that if the streets are not wet it, then it is not raining.



Hint: as you can see plainly, this is an implication. Structure you proof

accordingly. What do you assume to begin and what do you then need to show?

If what you need to show is itself an implication, follow the same strategy!

Assume that you have proof of the premise and show (in the context of all of

the assumptions you've made) that you can construct a proof of the conclusion.

-/



theorem contraPos : (P → Q) → (¬ Q → ¬ P) :=

begin

assume pq,

show ¬ Q → ¬ P,

from 

assume nq: ¬ Q,

show ¬ P,

from

assume p : P,

show false,

from nq (pq p)

end



/-

#11 -- 10 points



Using at most a few sentence in English, give concise answers to the

following two questions.





#11a: In a few words (within this comment block) explain the strategy of

proof by negation. Clearly state the form of the goal to be proved and how

exactly one proceeds to use proof by negation to prove it.



YOUR ANSWER HERE: Proof by negation is used to prove a proposition of the

form ¬ P. To use this strategy, one assumes P and shows that that leads to

a contradiction. (This shows that P → false which is the definition of ¬ P).





#11b: 

In a few words (within this comment block) explain the strategy of proof by

contradiction. Clearly state the form of the goal to be proved and how

exactly one proceeds to use proof by contradiction to prove it. In addition,

explain why (classical) double negation elimination is essential to enabling

proof by contradiction.



YOUR ANSWER HERE: Proof by contradiction is used to prove a proposition of

the form P. To use it, one assumes ¬ P and shows that doing so leads to a

contradiction. This proves ¬ ¬ P, which, in classical logic also proves P.



-/





/-

EXTRA CREDIT -- 5 points: In Lean write an axiom, called double_negation_elim,

that tells lean to accept double negation elimination as a valid inference

rule without a proof of validity.

-/



axiom double_negation_elim : ∀ P :
Prop, ¬ ¬ P → P.
