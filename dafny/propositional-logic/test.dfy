include "decision.dfy"
include "evaluation.dfy"
include "truth_table.dfy"
include "consequence.dfy"

module satisfiability_test
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
        var Pvar := mkPVar("P");
        var Qvar := mkPVar("Q");
        var Rvar := mkPVar("R");
    
        var P := pVarExp(Pvar);
        var Q := pVarExp(Qvar);
        var R := pVarExp(Rvar);
        var notR := pNot(R);
        var PorQ := pOr(P,Q);
        var PorQandnotR := pAnd(PorQ,notR);

        var ourExpr := showPExp(PorQandnotR);
        var varOrder := [Pvar, Qvar, Rvar];

        var yes: bool;
        var models: seq<pInterpretation>;

        yes, models := satisfiable(PorQandnotR);
        if yes 
        { 
            var s := showPExp(PorQandnotR);
            print ourExpr + " is satisfiable as witnessed by:\n";
            show_pInterps(models, varOrder);
        }
        else { print "It's not satisfiable.\n";}

        yes, models := unsatisfiable(PorQandnotR);
        if yes {print "It's unsatisfiable\n"; }
        else  
        {
            print ourExpr + " is not unsatisfiable, as witnessed by:\n";
            show_pInterps(models, varOrder);
        }

        yes, models := valid(PorQandnotR);
        if yes { print "It's valid\n"; }
        else 
        {
            print ourExpr + " is not valid as witnessed by:\n";
            show_pInterps(models, varOrder);
        }

        var context := [pImpl(P, Q), pImpl(Q,R)];
        var conclusion := pImpl(P,R);

        yes := isConsequence(context, conclusion);
        var cxstr := showPContext(context);
        var cnstr := showPExp(conclusion);
        print cxstr + (if yes then " |- " else " !|- ") + cnstr + "\n";
    }
}