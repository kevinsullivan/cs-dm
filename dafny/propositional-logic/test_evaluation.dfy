include "evaluation.dfy"


module bexptest
{
    import opened expression
    import opened interpretation
    import opened evaluation

    method Main()
    {
        /*
            let's build the expression (P \/ Q) /\ ~R
            in plain text, that's (P or Q) and (not R)
        */
        var P := mkVar("P");
        var Q := mkVar("Q");
        var R := mkVar("R");
    
        var Pexp := pVarExp(P);
        var Qexp := pVarExp(Q);
        var Rexp := pVarExp(R);
        var notRexp := pNot(Rexp);
        var PorQexp := pOr(Pexp,Qexp);
        var PorQandnotRexp := pAnd(PorQexp,notRexp);

        /*
            Now let's build an "interpretation."
            This is a binding of variables in our
            little language to Boolean values, in
            the form of a map.
        */
        var st: pInterp := map[
                                P := true, 
                                Q := false, 
                                R := false
                               ];

        // Finally, let's do a "smoke test"
        print "\nThe state is ", st, "\n";
        print "P is ", pEval(Pexp, st), "\n";
        print "Q is ", pEval(Qexp, st), "\n";
        print "R is ", pEval(Rexp, st), "\n";
        print "notR is ", pEval(notRexp, st), "\n";
        print "PorQ is ", pEval(PorQexp, st), "\n";
        print "PorQ_and_notR is ", pEval(PorQandnotRexp, st), "\n\n";
    }
}