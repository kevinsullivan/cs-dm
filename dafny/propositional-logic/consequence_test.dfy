

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

        // veryify sound rules of inference, and one unsound!
        var modusPonens  := (([pImpl(P, Q), P], Q),"\n");
        var modusTollens := (([pImpl(P, Q), pNot(Q)], pNot(P)), "\n");
        var affirmConseq := (([pImpl(P, Q), Q], P), "\n");
        var syllogism    := (([pImpl(P, Q), pImpl(Q, R)], pImpl(P, R)),"\n");
        var resolution   := (([pOr(P, Q), pOr(pNot(Q), R)], pOr(P, R)),"\n");
        var unit_resoln  := (([pOr(P,Q), pNot(Q)], P),"\n");
        var and_elim_l   := (([pAnd(P, Q)], P),"\n");
        var and_elim_r   := (([pAnd(P, Q)], Q),"\n");
        var and_intro    := (([P, Q], pAnd(P,Q)),"\n");
        var or_intro_l   := (([P], pOr(P, Q)),"\n");
        var or_intro_r   := (([Q], pOr(P, Q)),"\n");
        var dub_neg_elim := (([pNot(pNot(P))], P),"\n");
        var true_intro := (([], pTrue),"\n");

        checkAndShowSequent(modusPonens);
        checkAndShowSequent(modusTollens);
        checkAndShowSequent(affirmConseq);
        checkAndShowSequent(syllogism);
        checkAndShowSequent(resolution);  
        checkAndShowSequent(unit_resoln);  
        checkAndShowSequent(and_elim_l);  
        checkAndShowSequent(and_elim_r);  
        checkAndShowSequent(and_intro);  
        checkAndShowSequent(or_intro_l);  
        checkAndShowSequent(or_intro_r);  
        checkAndShowSequent(dub_neg_elim);  
        checkAndShowSequent(true_intro);  
    }
}
