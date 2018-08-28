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
have left to prove You will see that you've assumed
that P and Q are arbitrary propositions and that 
you have a proof of P ∧ Q. Apply the appropriate
elimination and introduction rules, first to obtain
the necessary "ingredients" for the final proof (by
eliminations), and then combine them together into
a proof of the concluding proposition, Q ∧ P. Note
that the conclusion is a conjunction. That tells you 
a lot about what kind of introduction rule you need
to use to complete the proof. It's not a bad idea
to work "top down" by incrementally filling in the
hole with expressions that can include new holes,
continuing this "refinement" process until your
proof is complete
-/
theorem and_commutes: ∀ (P Q: Prop), P ∧ Q → Q ∧ P :=
    λ P Q pf, 
        and.intro 
            (and.elim_right pf) 
            (and.elim_left pf)

/-
You can read and_commutes as a function that takes
three parameters, two propositions and a proof of
P ∧ Q, and that returns a proof of Q ∧ P.  Another
way to read it is as taking two propositions, P and
Q, and returning a proof of P ∧ Q → Q ∧ P. This is
a reading that helps when it comes to solving the
next problem. Here's a slightly different but wholly
equivalent way to write the same thing.
-/
theorem and_commutes': forall P Q: Prop, P ∧ Q → Q ∧ P :=
    λ P Q, 
        (λ pf, 
            and.intro 
              (and.elim_right pf) 
              (and.elim_left pf))
/-
The inner lambda, a function, *is* a proof that if you
are give a proof, pf, of P ∧ Q, you can always return a
proof of Q ∧ P, i.e., P ∧ Q → Q → P. The parentheses 
around the inner lambda are not necessary but are there 
to highlight the fact that when the outer function is 
given propositions, P and Q, it returns a proof of an
implication, that P ∧ Q → Q ∧ P. This proof is given by
the function that the inner lambda defines. 
-/


/- PROBLEM #2

As you can see from the definition of and_commutes 
it is basically a function (see the lambda) that takes
two propositions, P and Q, as arguments, and that then
returns a proof of P ∧ Q → Q ∧ P. No other proofs are
needed as arguments in this case, as the proposition
to be proved is logically valid.

In this problem you use the fact that and_commutes ca
be "called" to build the two proofs that do have to be
provided as arguments to an introduction rule to build 
a proof of the stated equivalence. 

Read and understand the statement of the theorem first, 
then read the partial proof. Complete it by replacing 
"sorry" with a proof of the required type. You might 
again want to start by replacing sorry with a hole, 
then check to see the context and goal for that hole. 
And finally fill it with an expression that produces 
the required proof.
-/
theorem and_commutes_2: forall X Y: Prop, X ∧ Y ↔ Y ∧ X := 
    λ (X Y: Prop),
     iff.intro 
        (and_commutes X Y) 
        (and_commutes Y X) 

/-
To intoduce a conclusion of the form A ↔ B (A iff B), you 
have to have proofs of the implication in each direction.
You have to have a proof that A → B and a proof that B ↔ A,
Wwe need proofs of both X ∧ Y → Y ∧ X and Y ∧ X → X ∧ Y.
Luckily, the and_commutes function returns proofs of just
this sort. If you give it propositions, A and B, it gives 
you back a proof of A ∧ B → B ∧ A. If you given it B and
A as arguments, in that reversed order, it gives you back
a proof of B ∧ A → A ∧ B. We call and_commutes twice, with
the propositions X and Y in the right order, to build the
two proofs needed for the iff.intro rule to construct a
proof of the given ↔ proposition.
-/


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
    λ p q r pq qr, 
        eq.symm 
            (eq.trans pq qr)




/- PROBLEM #5 

In Lean, write and prove a theorem, called pqp, that 
states that, for any propositions, P and Q,  P → Q → P.
-/
theorem pqp: forall P Q: Prop, P → Q → P :=
    λ P Q pfP pfQ, pfP

/-
The first trick to solving this problem is to 
consider the solution to be a function that takes
four arguments and that then returns a proof of P.
The arguments are the propositions (types), P and
Q, a proof (value) of (type) P, and a proof of Q.
Given that context, the function has to return a
proof of P. But there's already one right there 
in the context, so we just return *it*. 

Now think about P -> Q -> P in natural language.
It says, "If P is true, then if Q is true then P
is also true". If you start by assuming that P
is true, then you can direclty conclude that P 
is true. You don't really have to consider Q at
all. 
-/


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
  λ f, false.elim f

theorem fq: ∀ Q: Prop, false → Q := 
    λ Q pf, false.elim pf