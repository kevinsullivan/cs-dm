include "interpretation.dfy"
include "variables.dfy"
module truth_table
{
    import opened syntax
    import opened variables
    import opened interpretation

    /*
    This method returns a sequence of all possible
    interpretations for a given sequence of Boolean
    variables, in increasing order from all false to
    all true. Each interpretation is a map from each
    of the variables to that variable's bool value 
    under the given interpretation. In other words, 
    this method returns the "input" parts of each row 
    of a truth table for the given propositional
    variables. 
    */
    method truth_table_inputs(e: pExp) 
        returns (result: seq<pInterpretation>)
    {
        var vs := seqVarsIn(e);
        result := [];
        var interp := all_false_interp(vs);
        var i: nat := 0;
        var n := pow2(|vs|);
        while (i < n)
        {
            result := result + [interp];
            interp := next_interp(vs, interp);
            i := i + 1;
        }
        return result;
    }
    
    /*
        Return an interpretation for the variables in 
        the sequence vs such that every variable maps 
        to false.
    */
    method all_false_interp(vs: seq<pVar>) 
        returns (result: pInterpretation)
    {
        result := map[];
        var i := 0;
        while (i < | vs |)
        {
            result := result[ vs[i] := false ];
            i := i + 1;
        }

        return result;
    }

    /*
    Given a sequence of variables and an interpretation
    for those variables, computes a "next" interpretation.
    Treat the sequence of values as a binary integer and 
    increment it by one. Any variables in vs that are not
    in interp are ignored. Would be better to enforce a
    pre-condition to rule out this possibility.
    */
    method next_interp(vs: seq<pVar>, interp: pInterpretation) 
        returns (result: pInterpretation)
    {
        result := interp;
        var i := | vs | - 1;
        while (i >= 0 ) 
        {
            if (! (vs[i] in interp)) { return; }
            assert vs[i] in interp;
            if (interp[ vs[i] ] == false) 
            { 
                result := result[ vs[i] := true ];
                break; 
            } 
            else
            {
                result := result[ vs[i] := false ];
            }
            i := i - 1;
        }
        return result;
    }

    /*
    Compute and return 2^n given n.
    */
    function method pow2(n: nat): (r: nat)
        ensures r >= 1
    { 
        if n == 0 then 1 else 2 * pow2(n-1) 
    }
}