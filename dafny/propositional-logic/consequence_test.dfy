

include "consequence.dfy"

module consequence_test
{
    import opened variables
    import opened syntax
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

        // *semantic* verification of soundness of ND rules of inference
        var true_intro  := (([], pTrue),"pTrue is true without conditions");
        var false_elim  := (([pFalse],P),"if pFalse is true, anything goes\n");
        var and_intro   := (([P, Q], pAnd(P,Q)),"and introduction; like constructor\n");
        var and_elim_l  := (([pAnd(P, Q)], P),"and elimination (get left)\n");
        var and_elim_r  := (([pAnd(P, Q)], Q),"and elimination (get right)\n");
        var or_intro_l  := (([P], pOr(P, Q)),"or intro, given truth of left arg");
        var or_intro_r  := (([Q], pOr(P, Q)),"or intro, given truth of right arg\n");
        var or_elim     := (([pOr(P,Q),pImpl(P,R), pImpl(Q,R)],R),"proof by cases\n");
        var false_intro := (([pImpl(P,pFalse)],pNot(P)),"proof not P by contradiction");
        var impl_elim   := (([pImpl(P, Q), P], Q),"-> elimination (modus ponens)\n");
 
        // resolution rules of inference used in many theorem provers
        var resolution   := (([pOr(P, Q), pOr(pNot(Q), R)], pOr(P, R)),"resolution\n");
        var unit_resoln  := (([pOr(P,Q), pNot(Q)], P),"unit resolution\n");

        // rules valid in classical but not intuitionistic (constructive) logic 
        var double_not_elim := (([pNot(pNot(P))], P),"double negation elimination\n");
        var law_of_excluded_middle: named_sequent := (([],pOr(P, pNot(P))),"law of exluded middle\n");  // note: need explicit type declaration here
    
        // a few more valid and classically recognized rules of inference
        var syllogism    := (([pImpl(P, Q), pImpl(Q, R)], pImpl(P, R)),"syllogism\n");
        var modusTollens := (([pImpl(P, Q), pNot(Q)], pNot(P)), "modus tollens\n");

        // now for the refutation of some logical fallacies
        var affirm_conseq  := (([pImpl(P, Q), Q], P), "don't affirm the consequence!\n");
        var affirm_disjunct := (([pOr(P,Q), P],pNot(Q)),"don't affirm a dijunct!\n");
        var deny_antecedent := (([pImpl(P,Q)],pImpl(pNot(P),pNot(Q))),"don't deny the antecedent!\n");

        // And finally, identities (provable unconditionally, theorems) "COMING SOON"

        checkAndShowSequent(true_intro);  
        checkAndShowSequent(false_elim);  
        checkAndShowSequent(and_intro);  
        checkAndShowSequent(and_elim_l);  
        checkAndShowSequent(and_elim_r);  
        checkAndShowSequent(or_intro_l);  
        checkAndShowSequent(or_intro_r);  
        checkAndShowSequent(or_elim);  
        checkAndShowSequent(false_intro);          
        checkAndShowSequent(double_not_elim);  

        checkAndShowSequent(impl_elim);
        checkAndShowSequent(modusTollens);
        checkAndShowSequent(affirm_conseq);
        checkAndShowSequent(syllogism);
        checkAndShowSequent(resolution);  
        checkAndShowSequent(unit_resoln);  
    }
}
