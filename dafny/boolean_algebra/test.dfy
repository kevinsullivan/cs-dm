include "semantics.dfy"


module bexptest
{
    import opened expression
    import opened evaluation

    method Main()
    {
        /*
            let's build the expression (true \/ false) /\ ~false.
            In plain text, that's (true or false) and (not false).
        */
        var P := bTrue;
        var Q := bFalse;
        var R := bFalse;
        var notR := bNot(R);
        var PorQ := bOr(P,Q);
        var PorQandNotR := bAnd(PorQ, notR);

        /*
        If you print the term itself, you'll see a lot of cruft
        inserted by the compiler, but if you peer through it all,
        you can disern the structure of the term: it's an "and"
        "box" with two smaller values inside. Each of those is in
        turn a box. The first is an "or" box with "litTrue" and
        "litFalse" inside. The second's a "not" box with "litFalse"
        inside. Values of inductively defined types often have this
        kind of nested, recursive struture. 
        
        You can also draw such a structure as a (computer sciency)"tree". Here it would have "and" at the top, with two sub-
        trees, the first an "or" tree, the second, a "not" tree. The
        children of the "or" tree would be "true" and "false", and
        of the not tree, "false".
        */

        // Here we print the term. Warning: messy output.
        var out_prefix := show_bExp(PorQandNotR);
        var out_infix := show_bExp_infix(PorQandNotR);
        print "The expression (prefix notation) is ", out_prefix, "\n";
        print "In infix notation, it's: ",  out_infix, "\n";

        // Evaluating the expression yields its Boolean value!
        var v := bEval(PorQandNotR);
        print "\n\nIts value is ", v, "\n";
    }
}