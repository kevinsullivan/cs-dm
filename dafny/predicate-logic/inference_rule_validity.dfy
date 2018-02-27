include "decision.dfy"
include "evaluation.dfy"
include "truth_table.dfy"
include "consequence.dfy"

module test_consequence
{
    import opened syntax
    import opened evaluation
    import opened interpretation
    import opened truth_table
    import opened model
    import opened decision
    import opened consequence

    method Main()
    {
        /*
        Set up data for testing. Note that in our
        design, variables, of type propVar, are *not*
        themselves propositions. Rather, they are basic
        data used to construct variable proposition
        expressions.

        It's easier to represent interpretations using
        polymorphic maps when "variables" objects have
        their own type, than when they are a subset of
        the terms of our proposition expressions type, 
        prop. 
        
        We might want to find a different name for them
        to make it clearer that they're not propositions.
        */

        // define three raw variables, enough for simple tests
        var Pvar: propVar := mkPropVar("P");
        var Qvar := mkPropVar("Q");
        var Rvar := mkPropVar("R");
    
        // define three propositional "variable expressions"
        var P: prop := pVar(Pvar); 
        var Q := pVar(Qvar);
        var R := pVar(Rvar);

        // veryify sound rules of inference, and one unsound!
        var and_intro    := (([P, Q], pAnd(P,Q)), "and introduction\n");
        var and_elim_l   := (([pAnd(P, Q)], P), "and elimination left\n");
        var and_elim_r   := (([pAnd(P, Q)], Q), "and elimination right\n");
        var or_intro_l   := (([P], pOr(P, Q)), "or introduction left\n");
        var or_intro_r   := (([Q], pOr(P, Q)), "or introduction right\n");
        var or_elim      := (([pOr(P, Q), pImpl(P,R), pImpl(Q,R)], R),
                                "or elimination\n");

        var neg_intro    := (([pImpl(P, pFalse)], (pNot(P))), 
                                "negation introduction\n" );
        var dub_neg_elim := (([pNot(pNot(P))], P), 
                                "double negation elimination\n");

        var true_intro := (([], pTrue), "true introduction\n");
        var false_elim := (([pFalse], P), "false elimination\n");
        /*
        There is no "false introduction", as that would be tantamount
        to saying, "the impossible has been confirmed"
        */

        var impl_elim  := (([pImpl(P, Q), P], Q), 
                                "-> elimination (modus ponens)\n");
        var resolution   := (([pOr(P, Q), pOr(pNot(Q), R)], pOr(P, R)),
                                "resolution\n");
        var unit_resoln  := (([pOr(P,Q), pNot(Q)], P), 
                                "unit_resolution\n");


        // A few additional rules
        var modusTollens := (([pImpl(P, Q), pNot(Q)], pNot(P)), 
                                "modus tollens\n");
        var syllogism    := (([pImpl(P, Q), pImpl(Q, R)], pImpl(P, R)), 
                                "syllogism\n");

        /*
        The observant reader will have noticed that we provided no rule
        for implication introduction. The rule is something like this: if [P, Q] |- R is valid, then [Q] | P -> R is, too. This 
        makes sense. If knowing or assuming that P and Q are true
        enables one to deduce that R is true, then knowing or assuming that Q alone is true allows one to conclude P -> R, i.e., that if P is true (knowing that Q is) then it must be possible to 
        prove that R is, too. 
        
        This rule removes a premise from the context and makes it the premise of an implication in the conclusion. This maneuver is
        called "discharging" the *assumption* that P is true by making
        it a premise of an implication. 
        
        To express this idea in code, we'd have to be able to say not 
        only that "if the propositions in this context are true then 
        this conclusion is true, too", but "if this *sequent* is valid,
        then this one is, too". 
        
        To be able to express this idea precisely, we need a new little 
        language: not just a language of propositions with a semantics, 
        but a language proofs based on transformations of sequents, as
        we see in this case. 
        */

        print "\n\nSome Valid Rules of Inference\n";
        print "************************************\n";
        checkAndShowSequent(and_intro);  
        checkAndShowSequent(and_elim_l);  
        checkAndShowSequent(and_elim_r);  
        checkAndShowSequent(or_intro_l);  
        checkAndShowSequent(or_intro_r);  
        checkAndShowSequent(or_elim);  
        checkAndShowSequent(dub_neg_elim);  
        checkAndShowSequent(true_intro);  
        checkAndShowSequent(false_elim);
        checkAndShowSequent(impl_elim);
        checkAndShowSequent(resolution);  
        checkAndShowSequent(unit_resoln);  
        checkAndShowSequent(modusTollens);
        checkAndShowSequent(syllogism);

        /*
        Let's invalidate some fallacies.
        */
        var affirmConseq := (([pImpl(P, Q), Q], P), 
                                "affirm consequence -- don't do it!\n");
        var false_exclusion_of_disjunct := (([pOr(P,Q), P], pNot(Q)),"false exclusion of disjunct\n");
        var deny_antecedent := (([pOr(P,Q)], pImpl(pNot(P),pNot(Q))),"false denying antecedent (compare with modus tollens)\n");

        print "\n\nSome Logical Fallacies\n";
        print "*****************\n";
        checkAndShowSequent(affirmConseq);
        checkAndShowSequent(false_exclusion_of_disjunct);
        /*
        Turing example: "If each man had a definite set of rules of conduct by which he regulated his life he would be no better than a machine. But there are no such rules, so men cannot be machines."
        */
        checkAndShowSequent(deny_antecedent);
        

        /*
        Now we assert and check major algebraic properties of our
        operators. Because we do this for arbitrary propositions, 
        P, Q, and R, one can be assure that these properties hold
        no matter what P, Q, and are actually mean in the real world
        (e.g., maybe P means, "CS is massively awesome"; but it just
        doesn't matter).
        */
        var and_commutes_theorem  := (([], 
                                pAnd(pImpl(pAnd(P,Q),pAnd(Q,P)),
                                     pImpl(pAnd(Q,P),pAnd(P,Q)))), 
                                "P and Q is equivalent to Q and P\n");
        // why is explicit type needed here?
        var or_commutes_theorem: named_sequent  := (([], 
                                pAnd(pImpl(pOr(P,Q),pOr(Q,P)),
                                     pImpl(pOr(Q,P),pOr(P,Q)))), 
                                "P or Q is equivalent to Q or P\n");

        // associativity of and
        // associativity of or
        // double negation elimination (as equivalence)
        // contrapositive (P -> Q) <=> (~Q -> ~P)
        // implication elminiation (P -> Q) <=> ~P || Q
        // demorgan-and: ~(P /\ Q) <=> ~P \/ ~Q
        // demorgan-or: ~(P \/ Q) <=> ~P /\ ~Q
        // dist-and/or: P /\ (Q \/ R) <=> (P /\ Q) \/ (P /\ R)
        // dist-or/and: P \/ (Q /\ R) <=> (P \/ Q) /\ (P \/ R)


        print "\n\nAlgebraic Properties (Theorems)\n";
        print "*******************************\n";
        checkAndShowSequent(and_commutes_theorem);
        checkAndShowSequent(or_commutes_theorem);
        // etc.

    }
}