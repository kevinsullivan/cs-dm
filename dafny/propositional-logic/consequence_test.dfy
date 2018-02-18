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
        var modusPonens  := ([pImpl(P, Q), P],             Q);
        var modusTollens := ([pImpl(P, Q), pNot(Q)],       pNot(P));
        var affirmConseq := ([pImpl(P, Q), Q],             P);
        var syllogism    := ([pImpl(P, Q), pImpl(Q, R)],   pImpl(P, R));
        var resolution   := ([pOr(P, Q), pOr(pNot(Q), R)], pOr(P, R));
        var unit_resoln  := ([pOr(P,Q), pNot(Q)],          P);
        var and_elim_l   := ([pAnd(P, Q)],                 P);
        var and_elim_r   := ([pAnd(P, Q)],                 Q);
        var and_intro    := ([P, Q],                       pAnd(P,Q));
        var or_intro_l   := ([P],                          pOr(P, Q));
        var or_intro_r   := ([Q],                          pOr(P, Q));
        var dub_neg_elim := ([pNot(pNot(P))],              P);
        var true_intro: sequent := ([],                    pTrue);

        print "\n";
        checkAndShowSequent(modusPonens, "/* modus ponens */", true);
        print "\n";
        checkAndShowSequent(modusTollens, "/* modus tollens */", true);
        print "\n";
        checkAndShowSequent(affirmConseq, "/* affirm consequence */", true);
        print "\n";
        checkAndShowSequent(syllogism, "/* syllogism */",  true);
        print "\n";
        checkAndShowSequent(resolution, "/* resolution */",  true);  
        print "\n";
        checkAndShowSequent(unit_resoln, "/* unit resolution */",  true);  
        print "\n";
        checkAndShowSequent(and_elim_l, "/* and elim left */",  true);  
        print "\n";
        checkAndShowSequent(and_elim_r, "/* and elim right */",  true);  
        print "\n";
        checkAndShowSequent(and_intro, "/* and intro */",  true);  
        print "\n";
        checkAndShowSequent(or_intro_l, "/* or intro left */",  true);  
        print "\n";
        checkAndShowSequent(or_intro_r, "/* or intro right */",  true);  
        print "\n";
        checkAndShowSequent(dub_neg_elim, "/* double negation elimination */",  true);  
        print "\n";
        checkAndShowSequent(true_intro, "/* true introduction */",  true);  
        print "\n";
    }
}