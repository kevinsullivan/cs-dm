include "myblang.dfy"

import opened mb = myblang

/*
We have defined our own little language, both syntax and semantics
*/
method Main()
{
    /*
    We start by constructing three "variables", to which we
    give the convenient names, P, Q, and R. Henceforth we will
    refer to them using these names.
    */
    var P := V(0);
    var Q := V(1);
    var R := V(2);

    /*
    Now you are to build a term representing the Boolean expression
    (P \/ Q) /\ ~R. That is "(P or Q) and (not R)".
    */
    var T := bAnd(bOr(bVar(P),bVar(Q)),bNot(bVar(R))); // replace bFalse with the correct bExp value

    /*
    Next we construct an environment (a map) that associates a
    Boolean value with each of these variables.
    */
    var env1 := map[P := true, Q := false, R := false];

    /*
    And now finally we can evaluate our Boolean expression, T, in
    the environment, env1, to determine its truth value in the given
    environment. You must understand that to evaluate an expression
    that includes variables, you *must* provide an "environment" that
    "explains" what the value of each parameter is!
    */
    var result := bEval(T,env1);

    /*
    Print the result.    
    */
    print "The answer is ", bEval(T,env1), "\n";
}
