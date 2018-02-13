include "satisfiability.dfy"

include "satisfiability.dfy"
include "evaluation.dfy"

module satisfiability_test
{
    import opened bool_var
    import opened bool_interp
    import opened bool_syntax
    import opened bool_satisfiability
    import opened bool_eval

method Main()
    {
        var Pvar := mkVar("P");
        var Qvar := mkVar("Q");
        var Rvar := mkVar("R");
    
        var P := varExp(Pvar);
        var Q := varExp(Qvar);
        var R := varExp(Rvar);
        var notR := notExp(R);
        var PorQ := orExp(P,Q);
        var PorQandnotR := andExp(PorQ,notR);
        // print varsIn(PorQandnotR);

        var sat: bool;
        var interp: interpretation;
        sat, interp := satisfiable(PorQandnotR);
        if sat  { 
            print "\nSatisfied by: ";
            show(interp);
            print "\n\n"; 
        }
        var val;
        val, interp := valid(PorQandnotR);
        if !val  { print "\nInvalid. Counterexample: ";
            show(interp);
            print "\n\n"; 
        }

    }
}