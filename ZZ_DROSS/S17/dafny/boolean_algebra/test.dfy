include "semantics.dfy"


module bexptest
{
    import opened expression
    import opened evaluation

    method Main()
    {
        /*
            We now build a term of our bExp type represengin
            the expression "(true \/ false) /\ ~false", or, in
            plain text, "(true or false) and (not false)". We
            do this by first defining assigning the literal
            expressions, bTrue and bFalse, to Dafny variables
            P, Q, and R, which are thus of type bExp. Then we
            build larger expressions involving not, and, and
            or connectives using the corresponding constructors.
            The Dafny variable, PorQandNotR, ultimately has as
            its value a term of type bExp that represents the
            Boolean expression we seek to construct. You see
            here the "inductive" construction of a complex
            expression from smaller expressions ultimately 
            "bottoming out" in the base/literal expressions, 
            bTrue and bFalse.
        */
        var P := bTrue;
        var Q := bFalse;
        var R := bFalse;
        var notR := bNot(R);
        var PorQ := bOr(P,Q);
        var PorQandNotR := bAnd(PorQ, notR);

        /*
        If you were to print the term, PorQandNotR, using the Dafny
        command, "print PorQandNotR", you'd see a lot of "cruft"
        inserted by the compiler; but if you peer through it all,
        you would disern the structure of the term: it's a 2-tuple
        with label "bAnd" with two smaller expressions as its values. 
        Each is in turn a smaller term, or labelled tuple. The first 
        is an "or-labelled" tuple with two elements, "litTrue" and 
        "litFalse". The second's a "not-labelled" one-tuple with 
        "litFalse" inside. Values of inductive types generally have 
        this kind of recursive struture. 
        
        You can also draw such a structure as a "tree". Here it would 
        have "and" at the top, with two subtrees, the first an "or" 
        tree, the second, a "not" tree. The children of the "or" tree 
        would be "bTrue" and "bFalse", and of the not tree, "bFalse".
        */

        // Print the expression using prefix notation
        var out_prefix := show_bExp(PorQandNotR);
        print "In prefix notation: ", out_prefix, "\n";

        // Print the expression using infix notation
        var out_infix := show_bExp_infix(PorQandNotR);

        print "In infix notation: ",  out_infix, "\n";

        // Evaluate expression and print its "meaning"
        var v: bool := bEval(PorQandNotR);
        print "\n\nIts meaning (value) is ", v, "\n";
    }
}