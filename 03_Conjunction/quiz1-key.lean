/-
Here are three stylistically different
answers for the in-class quiz, in which
you were asked to prove that you could
derive a proof of (P ∧ (Q ∧ R)) from any
proof of ((P ∧ Q) ∧ R).

The first answer is in the form of an
exact proof term. It was developed by
top-down, type-guided decomposition. 
That's a technical way of saying that
we applied and.intro to two arguments,
then we "recursively" figured out what
each of those arguments had to be; and
we kept going with this approach until
we'd filled in all the blanks.

The second answer uses a tactic script,
which has the effect of constructing 
the same proof term. It applies and.intro
but now without arguments. Lean figures
out what the arguments has to be and 
tells you, making the production of 
those arguments into sub-goals. You
can see that this script effects the
the same kind of top-down "refinement"
as we saw above.
-/

/-
The final answer uses a more bottom-up
method. An even better name for it, as
we'll see is decompose-recompose. First
it extracts the needed "smaller" proofs
from the given proof using elimination
rules, then it uses introduction rules 
to combine those "ingredients" back in 
a different way to produce the proof 
that is sought.
-/

/-
In the end we thus see two strateies 
here: top-down refinement, using both
an exact proof term and a script; and
decompose-recompose using elimination
rules followed by introduction rules.
-/


/- ** Top-down refinement #1 ** -/

/-
Note: The name of argument, pfP_QR, in
the original version of this file was 
somewhat misleading. It named the given
proof of (P ∧ Q) ∧ R, i.e., the premise.
A better name would have been pfPQ_R. 
We've made that change in the code below.
-/

/-
Give a proof as an explicit proof value.
Use top-down, type-guided programming to
 to develop such a proof object. Look at
 the top connective in the proposition to
 be proved, and look for inference rules
 that allow you to prove propositions of
 that form. At present we have only one
 choice: the top-level introduction rule
 has to be and.intro, because we aim to
 prove a conjunction. That rule in turn
 takes two arguments, one a proof of P,
 and the other a proof of Q ∧ R. Now do
 the same thing for each of these proofs:
 figure out where you can get them from,
 in this case by applying elimination 
 rules to the given proof pfPQ_R. Keep
 up this top-down process until the proof
 is fully developed and complete.
-/

def and_assoc_r 
  { P Q R : Prop } 
  (pfPQ_R: (P ∧ Q) ∧ R) : 
    (P ∧ (Q ∧ R)) := 
    and.intro  
        (and.elim_left (and.elim_left pfPQ_R))
        (and.intro 
            (and.elim_right (and.elim_left pfPQ_R)) 
            (and.elim_right pfPQ_R))


/- ** Top-down refinement #2 ** -/

/-
In the next proof script, we start again by 
asking what is the form of the proposition to
be proved. The answer to this question tells
you a lot about how to go about constructing
a proof. The answer here is, "the proposition
is a a conjunction, with P on the left and 
(Q ∧ R) on the right.  

We thus begin by applying the and.intro rule (with
no arguments). This action sort of "runs the rule
in reverse" by telling us exactly what proofs are
needed to be able to apply and.intro to complete 
the proof. In this case, we end up with two sub-
goals to be proved: one for P, one for (Q ∧ R).

We deal with the top sub-goal (produce a proof for
P) first. On the second line, we give a complete
proof for P. 

That leaves the remaining goal of giving a proof 
for Q ∧ R. We one again apply and.intro to once
again split this goal into subgoals Q, and R.
The final two lines provide these proofs, first
one for Q and then one for R. This completes the
proof of (Q ∧ R).

With all the requisite sub-proofs ("ingredients")
now filled in, Lean checks and confirms that we
have a valid proof of (P ∧ (Q ∧ R)).
-/

def and_assoc_r'
  { P Q R : Prop } 
  (pfPQ_R: (P ∧ Q) ∧ R) : 
    (P ∧ (Q ∧ R)) :=
begin
apply and.intro,
exact (and.elim_left (and.elim_left pfPQ_R)),
apply and.intro,
exact (and.elim_right (and.elim_left pfPQ_R)),
exact and.elim_right pfPQ_R
end

/- ** Decompose / Recompose ** -/


/-
Finally, here is a more "bottom-up" script for
constructing a proof of (P ∧ (Q ∧ R)) given one
for (P ∧ Q) ∧ R).

The first line applies the right elimination
rule to the given proof to extract from it the
proof of R that it contains. The name, pfR, is
bound (given) to this proof.

The second "have" applies the left elimination
rule to obtain the constituent proof of (P ∧ Q).
The name pfPQ is given to this proof.

The third and fourth lines then apply elimination
rules to this pfPQ proof to extract proofs of P
and of Q, naming them pfP and pfQ.

You have now extracted from the given proof a
proof of P, of Q, and of R. The last "have" then
applies and.intro to pfQ and pfR to construct a
proof of (Q ∧ R). Finally the exact tactic gives
a proof of the final proposition by applying the
and.intro inference rule to pfP and pfQR. QED.

Notice the essential proof construction approach
we're using here: first use elimination rules to 
decompose (break down) the proof(s) that you're 
given to derive the (smaller) proofs you'll need 
to construct your final proof; then re-compose
those smaller proofs using introduction rules to
construct the proof you seek. We might call this 
the decompose/recompose (eliminate/introduce)
strategy of proof construction.  
 -/

def and_assoc_r''
  { P Q R : Prop } 
  (pfPQ_R: (P ∧ Q) ∧ R) : 
    (P ∧ (Q ∧ R)) :=
begin
have pfR := and.elim_right pfPQ_R,
have pfPQ := and.elim_left pfPQ_R,
have pfQ := and.elim_right pfPQ,
have pfP := and.elim_left pfPQ,
have pfQR := and.intro pfQ pfR,
exact and.intro pfP pfQR,
end

/-
Whether you're working with formal proofs using 
a tool like Lean or writing paper-and-pencil 
proofs, you will want to have in your toolkit
both of the proof strategies we have seen here.
The first strategy is top-down decomposition. It
works by applying introduction rules in reverse, which tells you what "input" proofs you need to 
be able finally to use the introduction rules 
to get the proofs you seek. The second is the
decompose/re-compose, or eliminate/introduce
strategy, where you use elimination rules to
extract from given proofs the smaller proofs 
you will need to finally apply the introduction
rules to construct the proofs you seek. It is
important to understand and to be able to use
both techniques. Real proof developments often
involve the mixed use of both techniques.
-/