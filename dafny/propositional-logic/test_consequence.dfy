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
        data used to construct variable propositions.
        It's easier to represent interpretations using
        polymorphic maps when these "variables" have
        their own type than when they are a subset of
        the terms of the proposition type, prop. We
        might want to find a different name for them
        to make it clearer that they're not themselves
        propositions.
        */

        // variables
        var Pvar: propVar := mkPropVar("P");
        var Qvar := mkPropVar("Q");
        var Rvar := mkPropVar("R");
    
        // propositions
        var P: prop := pVar(Pvar); 
        var Q := pVar(Qvar);
        var R := pVar(Rvar);
        var notR := pNot(R);
        var PorQ := pOr(P,Q);
        var PorQandnotR := pAnd(PorQ,notR);

        // variables for return results of decision procedures
        var yes: bool;

        var context := [pImpl(P, Q), pImpl(Q,R)];
        var conclusion := pImpl(P,R);

        yes := isConsequence(context, conclusion);
        var cxstr := showPContext(context);
        var cnstr := showProp(conclusion);
        print cxstr + (if yes then " |= " else " !|= ") + cnstr + "\n";
    }
}