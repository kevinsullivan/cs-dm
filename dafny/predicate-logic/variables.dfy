include "syntax.dfy"

/*
    This module is a helper module for our
    propositional logic syntax module. This
    module provides functions for dealing
    with variable objects and variable terms
    in our logic.
    
    In the usual definition of propositional
    logic, an "interpretation" is a mapping
    from a subset of terms, namey variable
    terms, to corresponding Boolean values.
    
    It's easier to define and manage this
    mapping when "variables" are of their
    own type, as is the case here, rather
    than being a subset of terms of another
    type (namely prop, i.e., logical terms).
    
    Thus in our design we have a separate 
    propVar type, and instance of which is
    required to create a variable *term* in
    our logic. 
    */

    
module variables
{
    import opened syntax

    method seqVarsInProp(e: prop) returns (result: seq<propVar>)
    {
        /* Compute the set of variables the convert to sequence
           Dafny does not allow expressions in return statements
           so we compute and store the results of the expression
           first, and then return
        */

        result := varSetToSeq(getVarsInProp(e));
        return;
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
    method varSetToSeq(s: set<propVar>) returns (result: seq<propVar>)
    {
        var l: seq<propVar> := [];
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
    To write the specification for the method that 
    gathers all the variables in a given proposition
    and returns them as a set, we need a predicate
    that tells us whether a given variable appears
    in a given proposition. That's what this function
    does. A variable, v, never appears in any literal 
    pTrue or pFalse expression. It appears in a variable
    expression if and only if it's the same variable.
    Otherwise it appears in an expression built using
    a connective iff it appears in any subexpression.
    */
    predicate method varInExp(v: propVar, e: prop)
    {
        match e 
        {
            case pFalse => false
            case pTrue => false
            case pVar(v') => v'.name == v.name
            case pNot(e') => varInExp(v,e')
            case pAnd(e',e'') => varInExp(v,e') || varInExp(v,e'')
            case pOr(e',e'') => varInExp(v,e') || varInExp(v,e'')
            case pImpl(e',e'') => varInExp(v,e') || varInExp(v,e'')   
        }
    }

    /*
    Given a prop, we will often need to extract from it
    the set of variables it uses. This method does that.
    Note that even if a variable appears multiple times 
    in an expression it will of course only appear in the
    set once. The postcondition of this function is that
    the set of returned variables contains a variable iff
    that variables appears in the given expression.
    */
    function method getVarsInProp(e: prop): (r: set<propVar>)
        ensures forall v :: v in r <==> varInExp(v,e)
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
    function method getVarsHelper(e: prop, r: set<propVar>): set<propVar>
    {
        match e
        {
            case pFalse => r
            case pTrue => r
            case pVar (v: propVar) => r + { v }
            case pNot (e: prop) => r + getVarsInProp(e)
            case pAnd (e1: prop, e2: prop) =>
                r + getVarsInProp(e1) + getVarsInProp(e2)
            case pOr (e1: prop, e2: prop) =>
                r + getVarsInProp(e1) + getVarsInProp(e2)
            case pImpl (e1: prop, e2: prop) =>
                r + getVarsInProp(e1) + getVarsInProp(e2)
        }
    }

    /*
    Returns set of variables in a sequence of propositions.
    Useful in computing truth table for a set of propositions,
    as occur in contexts in relation to logical consequence.
    */
    method getVarsInProps(ps: seq<prop>) returns (result: set<propVar>)
    {
        var i := |ps| - 1;
        var varSet: set<propVar> := {};
        while (i > 0)
        {
            varSet := varSet + getVarsInProp(ps[i]);
            i := i - 1;
        }
        return varSet;
    }

    method seqVarsInProps(ps: seq<prop>) returns (result: seq<propVar>)
    {
        var varSet := getVarsInProps(ps);
        var varSeq := varSetToSeq(varSet);
        return varSeq;
    }

    method showVar(v: propVar) returns (r: string)
    {
        return v.name;
    }

    method showVars(vs: seq<propVar>, sep: string) returns (r: string)
    {
        var i := 0;
        var res := "";
        while (i < |vs|)
        {
            var showv := showVar(vs[i]);
            res := res + showv + sep;
            i := i + 1;
        }
        return res;
    }

    method foo(n: nat) returns (f: nat)
    {
        if (n == 0) { return 0; }
        else
        {
            var t := foo(n-1);
            return t;
        } 
    }
}