/-
PART I: LOGIC AND PROOF USING THE LEAN PROVER
This section is worth 20% of the exam grade.
There are five problems and one extra credit
problem.
-/



/- PROBLEM #1

Complete the proof by replacing the "sorry" stub
with code to construct a proof of the proposition.
You may want to start by replacing sorry with a 
hole (underscore), then hover over the underscore
to see what assumptions you've got and what you 
have left to prove. You will see that you've assumed
that P and Q are arbitrary propositions and that 
you have a proof of P ∧ Q. Apply the appropriate
elimination and introduction rules, first to obtain
the "smaller proofs" you'll need to construct the
desired proof (by using elimination rules), then 
apply an introduction rule to get the result you
need. The conclusion is a conjunction. That tells 
you what kind of introduction rule you need to use 
to complete the proof. It's not a bad idea to work 
"top down" by incrementally filling in the hole with 
expressions that can include new holes, continuing 
this "refinement" process until your proof is done.
-/
theorem and_commutes: forall P Q: Prop, P ∧ Q → Q ∧ P :=
    λ P Q pf, sorry



/- PROBLEM #2

As you can see from the definition of and_commutes 
it is basically a function (see the lambda!) that takes
two propositions, P and Q, as arguments, and that then
returns a proof of P ∧ Q → Q ∧ P. No other proofs are
needed as arguments in this case, as the proposition
to be proved is logically valid.

In this problem you use the fact that and_commutes can
be "called" to build the two proofs that you will need
to construct a proof of the stated equivalence. Recall
than equivalence is written as both iff and as ↔. 

Read and understand the statement of the theorem first, 
then read the partial proof. Complete it by replacing 
"sorry" with a proof of the required type. You might 
again want to start by replacing sorry with a hole, 
then check to see the context and goal for that hole. 
And finally fill it with an expression that produces 
the required proof. Hint: The rule you need to apply 
is of course the introduction rule for ↔, also known
as "iff".  
-/
theorem and_commutes_2: forall X Y: Prop, X ∧ Y ↔ Y ∧ X := 
    λ (X Y: Prop),
     iff.intro (and_commutes X Y) _




/- PROBLEM #3

Replace sorry to complete the proof that if p, q, and r
are arbitrary natural numbers, and p < q and q < r then 
p < r. Very strong hint: Lean already has a theorem (a
rule), called lt.trans, that when given a proof of p < q
and a proof of q < r generates a proof of p < r. 
-/
theorem my_lt_trans: ∀ p q r: nat, p < q → q < r → p < r :=
    λ p q r pq qr, lt.trans pq qr




/- PROBLEM #4

In Lean, write and prove the proposition that, for all 
natural numbers,  p, q, and r, if p is equal to q then 
if q is equal to r, then r is equal to p. Don't reverse 
the order of variables in this expression when writing 
it in Lean. If we were just restating transitivity of 
equality, the third proposition would have been p = r, 
but here it's r = p. Hint: compose inference rules for
two different properties of equality. Give your theorem
the name, eq_rev_trans
-/
-- your answer here
theorem eq_rev_trans: ∀ p q r: nat, p=q → q=r → r=p :=
    λ p q r pq qr, _




/- PROBLEM #5 

In Lean, write and prove a theorem, called pqp, that 
states that, for any propositions, P and Q,  P → Q → P.
-/
-- your answer here
theorem pqp: forall P Q: Prop, P → Q → P :=
  _




/- EXTRA CREDIT.

One of the inference rules that we did validate in 
the propositional logic unit, and that was described
in intro.lean, but that we did not have time to talk
about in class, states that false implies anything at 
all, even absurdities. Your task here is, in Lean, 
first to write and prove that false implies 0=1 (call 
the theorem f01) and then to write and prove a second 
theorem asserting that from false you can prove any 
proposition, Q, whatsoever (call it fQ).
-/

theorem f01: false → 0=1 := 
    sorry

-- Your answer for the second part here