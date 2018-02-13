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
    
        var Pexp := varExp(P);
        var Qexp := varExp(Q);
        var Rexp := varExp(R);
        var notRexp := notExp(Rexp);
        var PorQexp := orExp(Pexp,Qexp);
        var PorQandnotRexp := andExp(PorQexp,notRexp);

        /*
            Now let's build an "interpretation."
            This is a binding of variables in our
            little language to Boolean values, in
            the form of a map.
        */
        var st: Binterp := map[
                                P := true, 
                                Q := false, 
                                R := true
                               ];

        // Finally, let's do a "smoke test"
        print "\nThe state is ", st, "\n";
        print "P is ", Beval(Pexp, st), "\n";
        print "Q is ", Beval(Qexp, st), "\n";
        print "R is ", Beval(Rexp, st), "\n";
        print "notR is ", Beval(notRexp, st), "\n";
        print "PorQ is ", Beval(PorQexp, st), "\n";
        print "PorQ_and_notR is ", Beval(PorQandnotRexp, st), "\n\n";
    }
}