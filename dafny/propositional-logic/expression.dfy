module expression
{
    /*
        Now we define the *syntax* of a little language 
        of Propositional Logic.
    */


    /*
    We define an infinite set of "propositional
    variables" as terms of the form mkVar(s), and 
    of type, pVar.
    */

    datatype pVar = mkVar(name: string) 

    /*
    Note to instructor-self: This method not used.
    */
    function method pVar_name(b: pVar): string 
    {
        match b
        {
            case mkVar(s: string) => s
        }
    }

    
   /*
   The syntax of our language of propositions.
   */
    datatype pExp = 
        // variable expressions
        pVarExp (v: pVar) | 

        // operator application expression
        pNot (e: pExp) |
        pAnd (e1: pExp, e2: pExp) |
        pOr (e1: pExp, e2: pExp)


    
    /*
    The rest of this module implements two methods,
    one of which returns the *set* of variables in a
    given expression, and the other of which converts
    that set into a sequence and returns it. It is 
    much easier to work with sets than with sequences
    when collecting the variables in an expression.
    We don't want to include a variable more than once
    when the same variable occurs in two sub-expressions.
    But some of the code that uses this module will need 
    an ordered collection, i.e., a sequence, of all the
    variables, so we provide a function that converts a
    set into a sequence.
    */

    /*
    First, given a pExp, return a *set() containing all 
    and only the variables that appear in the expression. 
    A set contains a given element at most one time, so 
    even if a variable appears multiple times in a given
    expression, it'll be in the resulting set only once.
    */
    function method setVarsIn(e: pExp): set<pVar>
    {
      /*
      Do the work by calling a helper function with an
      empty sequence as the starting value. This "design 
      pattern" is typical: one implements a call to a
      a non-recursive function (this one) that then calls 
      a recursive function with some extra arguments to
      actually do the work.
      */
      setVarsInHelper(e, {})
    }

    /*
    This recursive function adds the set of variables in a 
    given expression to the set, r, given as an argument. So, 
    to get a set of the variables in a given expression, call 
    this function with the expression and with an empty set. 
    This is just what the "top-level" function above does.

    This code exhibits a second fundamental algorithm design
    pattern: mutual recursion. It doesn't call itself recursively,
    but, in cases where there's more work to do, calls the top-level 
    method (that called it). This recursive call to the top level
    computes the set of variables for the *subexpression* being
    processed by calling this method again. This method then 
    combines that result, passed in as *r*, with the results 
    obtained so far (represented in r) to compute the final 
    answer. 
    */
    function method setVarsInHelper(e: pExp, r: set<pVar>): set<pVar>
    {
        match e
        {
            // a var expression adds the variable it not yet there
            case pVarExp (v: pVar) => r + { v }
  
            // add, or , and not expression adds the variables below 
            case pNot (e: pExp) => r + setVarsIn(e)
            case pAnd (e1: pExp, e2: pExp) =>
                r + setVarsIn(e1) + setVarsIn(e2)
            case pOr (e1: pExp, e2: pExp) =>
                r + setVarsIn(e1) + setVarsIn(e2)
        }
    }

    /*
    This method gets the *set* of variables in a given
    expression and returns it as an ordered sequence. The
    order in which the elements will appear is undefined.
    That is, they will be in some order, but one must not
    count on there being any particular order. 
    */
    method seqVarsIn(e: pExp) returns (result: seq<pVar>)
    {
        /* Compute the set of variables the convert to sequence
           Dafny does not allow expressions in return statements
           so we compute and store the results of the expression
           first, and then return
        */

        result := setVarsToSeq(setVarsIn(e));
        return /* result */;
    }

    /*
    Given a set of propositional variables, convert it into a 
    sequence in some arbitrary order by calling a recursive 
    helper function with an initially empty sequence. This is 
    a second example of the design pattern seen above.
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
}