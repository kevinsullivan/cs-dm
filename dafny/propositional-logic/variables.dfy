include "syntax.dfy"

module variables
{
    import opened syntax

        method seqVarsIn(e: pExp) returns (result: seq<pVar>)
    {
        /* Compute the set of variables the convert to sequence
           Dafny does not allow expressions in return statements
           so we compute and store the results of the expression
           first, and then return
        */

        result := setVarsToSeq(getVars(e));
        return /* result */;
    }

    /*
    Given a set of propositional variables, convert it into a 
    sequence in some arbitrary order by calling a recursive 
    helper function with an initially empty sequence. This is 
    a second example of the design pattern seen above.

    Note that Dafny requires the *decreases* statement in the
    loop specification, to help it know how to prove that the
    loop terminates. The statement tells Dafny that it is the
    set, s', that "gets smaller until ulimately bottoming out"
    at the empty set. 
    */
    method setVarsToSeq(s: set<pVar>) returns (result: seq<pVar>)
    {
        var l: seq<pVar> := [];
        var s' := s;
        while (s' != {}) 
            decreases s';
        {
            var v :| v in s';
            l := [ v ] + l;
            s' := s' - { v };
        }
        return l;
    }

/*
    Given a pExp, we will often need to extract from it
    the set of variables it uses. This method does that.
    Note that even if a variable appears multiple times 
    in an expression it will of course only appear in the
    set once.
    */
    function method getVars(e: pExp): set<pVar>
    {
      /*
      Do the work by calling a recursive helper 
      function with an empty set as the starting 
      set to which the variables in the expression
      will be added.
      */
      getVarsHelper(e, {})
    }

    /*
    This recursive function adds the set of variables in a 
    given expression to the set, r, given as an argument. 
    Note: The getVars and getVarsHelper functions together
    exhibits a fundamental design pattern called "mutual 
    recursion". The main function calls the helper function
    with a partial result to be completed, then the helper
    function calls the main function recursively to solve
    sub-parts of the problem it was called to handle. It
    then combines the results of these subcalls to complete
    the work it was asked to do.  
    */
    function method getVarsHelper(e: pExp, r: set<pVar>): set<pVar>
    {
        match e
        {
            case pFalse => r
            case pTrue => r
            case pVarExp (v: pVar) => r + { v }
            case pNot (e: pExp) => r + getVars(e)
            case pAnd (e1: pExp, e2: pExp) =>
                r + getVars(e1) + getVars(e2)
            case pOr (e1: pExp, e2: pExp) =>
                r + getVars(e1) + getVars(e2)
            case pImpl (e1: pExp, e2: pExp) =>
                r + getVars(e1) + getVars(e2)
        }
    }

 
}