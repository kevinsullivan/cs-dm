include "decision.dfy"
include "evaluation.dfy"
include "truth_table.dfy"
include "consequence.dfy"

module test_sat
{
    import opened syntax
    import opened evaluation
    import opened interpretation
    import opened truth_table
    import opened model
    import opened decision
    import opened consequence
    import opened variables

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
        var Tvar := mkPropVar("T");
    
        // propositions
        var P: prop := pVar(Pvar); 
        var Q := pVar(Qvar);
        var R := pVar(Rvar);
        var T := pVar(Tvar);
        var notR := pNot(R);
        var PorQ := pOr(P,Q);
        var PorQandnotR := pAnd(PorQ,notR);
        var PQRT := pOr(PorQandnotR,T); // ((P \/ Q) /\ (~R)) \/ T
        

        // variable sequence for printing interpretations
        var varOrder := [Pvar, Qvar, Rvar, Tvar];

        // printable string for proposition
        var ourVars: string := showVars(varOrder, "\t");
        var ourExpr: string := showProp(PQRT);

        print ourVars + " " + ourExpr + "\n";

        // Print a truth table
        show_truth_table_for_prop(PQRT,varOrder,false);

        /*
        Here are the actual test calls to the various
        decision procedures. We set up yes and models
        as variables to hold return results for each of
        the three solver tests.
        */

        // variables for return results of decision procedures
        var yes: bool;
        var models: seq<pInterpretation>;


        // test satisfiability solver / model finder
        yes, models := satisfiable(PQRT);
        if yes 
        { 
            var s := showProp(PorQandnotR);
            print ourExpr + " is satisfiable as witnessed by:\n";
            show_interpretations(models, varOrder, false);
        }
        else { print "It's not satisfiable.\n";}


        // test unsatisfiability checker
        yes, models := unsatisfiable(PQRT);
        if yes {print "It's unsatisfiable\n"; }
        else  
        {
            print ourExpr + " is not unsatisfiable, as witnessed by:\n";
            show_interpretations(models, varOrder, false);
        }


        // test validity checker
        yes, models := valid(PQRT);
        if yes { print "It's valid\n"; }
        else 
        {
            print ourExpr + " is not valid as witnessed by:\n";
            show_interpretations(models, varOrder, false);
        }
    }
}