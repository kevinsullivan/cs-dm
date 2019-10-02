/-
THIS ASSIGNMENT IS DUE BEFORE 9AM 
ON TUESDAY NEXT WEEK, BEFORE THE 
DAY'S 2101 CLASSES BEGIN. WE WILL 
REVIEW THE ANSWERS IN CLASS. THEN 
WE WILL GIVE An IN-CLASS, GRADED 
EXERCISE TO TEST YOUR UNDERSTANDING.

This file comes in two parts. The first
part presents an example that you are to
read and understand. It's an example of 
a proof of a bi-implication between two
equivalent disjunctions. The key lesson 
it teaches is proof by *case analysis*.

When you are asked to prove that P ∨ Q 
implies some conclusion, you do it by 
case analysis. The idea is that if P ∨ Q 
is true, there are two ways in which it
can be true: either P is true, or Q is 
true. You have prove the goal follows 
in either case. If the goal follows in 
either case,  then it follows from the 
disjunction, P ∨ Q, as a whole. 

We use the "cases" tactic in lean to 
reason about the two possible cases of
a proof of P ∨ Q. Using this tactic 
produces two subgoals. In one case, P 
is assumed to have a proof, p. In the
other case, Q is assumed to have a proof,
q. The aim then is to show that the main
goal follows in each case, as that will
then prove that the goal follows from 
the disjunction as a whole.

The second part of this file presents a
problem for you to solve. One again it's
a bi-implication involving a disjunction
as a premise (in one direction but not in
the other direction). 

In both of these parts, we, or you will, 
start by applying iff.intro to split the 
bi-implication into two implications to be proved. 

Then in the subproblems with disjunctions 
as premises, you will use case analysis. 
A hint: Remember that ¬ X means X → false,
and the way to prove this is to assume X
and show this leads to a contradiction. It
is this maneuver that gets you a disjunction 
as a premise in the problem you're to solve.
-/


-- PART I: A WORKED EXAMPLE

/-
We first show you how to prove P ∨ Q ↔ Q ∨ P.
At the highest level, the proof is by showing
the implication in each direction. Within each
direction, the proof is by case analysis for 
the disjunction that forms the premise of the
implication. These ideas are explained in more
detail in the proof that follows.
-/

theorem 
or_commutes :  
    ∀ P Q: Prop, P ∨ Q ↔ Q ∨ P 
:=
begin

/-
Introduce the assumptions that P and Q
are arbitrary propositions.
-/
assume P Q: Prop,

/-
To prove a bi-implication, we prove the
implications in each direction. That is, 
we break the overall goal into subgoals, 
one for the forward implication and one
for its converse (in the other direction).
-/
apply iff.intro,

    -- now we prove the forward implication
    assume pq : P ∨ Q,
    show Q ∨ P,
    from
        begin
        /-
        The key proof technique for reasoning 
        from a proof of a disjunction, P ∨ Q,
        is to consider two possible cases for 
        this proof, that either P is true or 
        Q is, and to show that the goal is
        true in either case. This shows that
        no matter why P ∨ Q is true, the goal
        follows.
    
        So, the proof strategy is first to 
        assumes that P ∨ Q is true because P 
        is true, which is to say you assume 
        you have a proof of P, and then show 
        that the goal follows. Then you assume 
        P ∨ Q is true because Q is true, and 
        you show that given an assumed proof
        of Q, the goal follows. The goal thus
        follows in either case. 

        The tactic that we use in Lean to 
        reason by cases from a disjunction is 
        called "cases." As arguments you give 
        it (1) the name of the disjunction to 
        reason from, and (2) names to use for 
        the assumed proofs of P and Q in the 
        respective cases (after keyword "with").  

        So here we go. Make sure you have the 
        Lean Messages window open so that you 
        can see how "cases" changes your tactic 
        state. Note that it introduces two new 
        subgoals. In the first, there is an 
        assumed proof, p : P. In the second, 
        there is an an assumed proof q : Q.
        -/
        cases pq with p q,
        -- now prove each case separately

            -- proof for case where P is true
            show Q ∨ P,
            from or.intro_right Q p,

            -- proof for case where Q is true
            show Q ∨ P,
            from or.intro_left P q,
        end,
    
    -- and now we prove the converse
    assume qp : Q ∨ P,
    show P ∨ Q,
    from 
        begin
        cases qp with q p,
            show P ∨ Q,
            from or.intro_right P q,
            show P ∨ Q,
            from or.intro_left Q p,
        end,
end



-- PART II: YOUR HOMEWORK ASSIGNMENT

/-
Homework: 

Prove, ∀ P Q: Prop, ¬ P ∧ ¬ Q ↔ ¬ (P ∨ Q) 

-/

theorem aDemorganLaw : 
    ∀ P Q: Prop, ¬ P ∧ ¬ Q ↔ ¬ (P ∨ Q) :=
begin
_
end