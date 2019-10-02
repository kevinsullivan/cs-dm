/-
Prove P ∨ Q ↔ Q ∨ P.
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

/-
Homework: 

Prove, ∀ P Q: Prop, ¬ P ∧ ¬ Q ↔ ¬ (P ∨ Q) 

-/

theorem aDemorganLaw : ∀ P Q: Prop, ¬ P ∧ ¬ Q ↔ ¬ (P ∨ Q) :=
begin
assume P Q : Prop,
apply iff.intro,

-- forward
assume npnq,
show ¬(P ∨ Q), 
from
    begin
    assume poq,
    -- proof by cases
    cases poq with p q,
    -- case where P is true
    show false, from npnq.left p,
    -- case where Q is true
    show false, from npnq.right q,
    end,

-- converse
assume poq,
show  ¬P ∧ ¬Q,
from 
    begin
    -- proof by and introduction
    apply and.intro,
    -- left conjunct
    assume p, show false, from poq (or.intro_left Q p),
    -- right conjunct
    assume q, show false, from poq (or.intro_right P q)
    end,
-- QED
end