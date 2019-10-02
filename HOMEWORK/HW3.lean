/-
This homework assignment will be due in class
on Thursday, September. Edit your answers into
this file and save your answers. Know where 
the file is in your file system so that you
can submit it to Collab during class. To be
ready for this homework, you should be sure
to have read all of the class material up to
and including 03_Conjunction, and you should
have (on your own or in class) done all of 
the exercises in those units. 
-/

/-
1. Produce a proof, pf1, of the proposition
that 0 = 0 ∧ (1 = 1 ∧ 2 = 2).
-/

-- WRITE ANSWER HERE

/-
2. Produce a proof, pf2, of the proposition
that (0 = 0 ∧ 1 = 1) ∧ 2 = 2
-/

-- WRITE ANSWER HERE


/-
3. Produce a proof, pf3, of the proposition
that 0 = 0 ∧ 1 = 1 ∧ 2 = 2. Hint, one of
the two preceding proofs can be used to
prove this proposition; there's no need
to type out a whole new proof.
-/

-- WRITE ANSWER HERE

/-
4. An operator, *, is "right associative"
if X * Y * Z means X * (Y * Z), and is
"left associative" if X * Y * Z means
(X * Y) * Y. Is the logical connective,
∧, left or right associative? Explain.
-/

-- WRITE ANSWER HERE

/-
5. Use Lean to produce a proof, pf4, that 
0 = 0 ∧ 1 = 1 ∧ 2 = 2 is exactly the
same proposition as one of the two
parenthesized forms. It will be a 
proof that two propositions are equal.
Put parentheses around each of the
propositions.
-/

-- WRITE ANSWER HERE


/-
6. Given arbitrary propositions, P, Q and
R it should be possible to produce a
proof, pf5, showing that if P ∧ (Q ∧ R)
is true then so is (P ∧ Q) ∧ R. Written
in inference rule form, this would say 
the following:

{ P Q R: Prop }, p_qr: P ∧ (Q ∧ R)
---------------------------------- ∧.assoc_l
          pq_r : (P ∧ Q) ∧ R

Proving that this is a valid rule 
can be done by defining a function, 
let's call it and_assoc_l, that when 
given any propositions, P, Q, and R 
(implicitly), and when given a proof 
of P ∧ (Q ∧ R), constructs and returns
a proof of (P ∧ Q) ∧ R. 

Here we give you this function, and
we explain each part in comments. 
You will then apply what you learn 
by studying this example to solve 
the same problem but going in the
other direction. Here's the solution.
-/

-- define the function name
def and_assoc_l 
-- specify the arguments and their types
        {P Q R: Prop} 
        (pf: P ∧ (Q ∧ R)) : -- note colon

-- the return type 
        (P ∧ Q) ∧ R
/-
What we've given so far is what we call
the function signature: its name, the
names and types of the arguments that it
takes, and the type of the return value.
In this case, the return value is of 
type (P ∧ Q) ∧ R, and will thus serve
as a proof of this proposition. This is
a function that takes a proof and returns
a (different) proof. It thus provides a
general recipe for turning any proof of
P ∧ (Q ∧ R) into a proof of (P ∧ Q) ∧ R.
-/ 
        :=  -- now give function body

/-
Usually we'd expect to see an expression
here, involving multiple, nested and.elim 
and and.intro expressions. We could write
the function body that way, but it's a bit
tricky to get all the nested expressions
right. Here's a revelation: We can use a
tactic script to produce the same result.

Open your Messages window, put your cursor
on begin, study carefully the tactic state,
notice that the arguments are given in the
context to the left of the turnstile and
the goal remaining to be proved is to the
right. You can use the context values as
arguments to tactics.

Now click through each line of the script
and study very carefully how it changes the
context. By the end of the script, you 
should see how we've been able to use 
elimination rules take apart the proof 
that was given as an argument, giving names 
to the parts, and how we can then further 
take apart those parts, giving names to the 
subparts, and finally how we can intro 
rules to put all these pieces together
again into the proof we need. 
-/
    begin
    have pfP := and.elim_left pf,
    have pfQR := and.elim_right pf,
    have pfQ := and.elim_left pfQR,
    have pfR := and.elim_right pfQR,
    have pfPQ := and.intro pfP pfQ,
    have pfPQ_R := and.intro pfPQ pfR,
    exact pfPQ_R
    end

/-
Define another function, and_assoc_r,
that goes the other direction: given
a proof of (P ∧ Q) ∧ R it derives and
returns a proof of P ∧ (Q ∧ R). Write 
the entire solution yourself.
-/

-- WRITE ANSWER HERE


/-
7. It's important to learn how you would
give such proofs in natural langage.
Let's take our first example. Here is
a natural language version.

"Given arbitrary propositions, P, Q, and
R, and the assumption that P ∧ (Q ∧ R) is
true, we are to show that (P ∧ Q) ∧ R is
true.

Given that P ∧ (Q ∧ R) is true, it must 
be that P is true and that Q ∧ R is also
true. Given that Q ∧ R is true, it must
be that Q is true, and R is also true.
So we have that P, Q, and R are all true.

From these conclusions we can in turn
deduce that P ∧ Q must be true. And so
we now have that P ∧ Q is true and so is
R, from which, finally we can deduce 
that (P ∧ Q) ∧ R must be true as well.

QED."

Now it's your turn: write an English
language proof for the theorem in the 
other direction.
-/

-- WRITE ANSWER HERE


/-
8. Use Lean to produce a proof, tnott, of
the proposition that truth isn't truth. 
I.e., true is not true. We'll write this
is Lean like this:

theorem tnott: true ≠ true := _. 

To make it a little easier to solve 
this otherwise difficult problem, we
allow you to stipulate one "axiom" of
your choice, which you can then use
to produce the required proof.
-/


-- WRITE ANSWER HERE
-- You can introduce an axiom here
-- Now prove the theorem here


/-
What did you have to accept to be able 
to prove that truth isn't truth?
-/

-- YOUR ANSWER HERE