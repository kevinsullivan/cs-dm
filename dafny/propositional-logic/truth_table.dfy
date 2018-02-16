include "interpretation.dfy"

module truth_table
{
    import opened syntax
    import opened interpretation

    /*
    This method returns a sequence of all possible
    interpretations for a given sequence of Boolean
    variables, in increasing order from all false to
    all true. Each interpretation is a map from each
    of the variables to that variable's value under
    the given interpretation. In other words, this
    method returns the "input" parts of each row of 
    a truth table for the given sequence of Boolean
    variables. We'll introduce a type synonym to
    express this abstraction. 
    */

    type truthTableInputs = seq<pInterpretation>
    // plus constraint that all combinations are represented

    /*
    A currently unverified precondition is that no
    variable may occur in "vs" more than once.
    */
    method all_interps(e: pExp) 
        returns (result: truthTableInputs)
        // requires forall v :: | (toBag(vs))[v] <= 1 |
    {
        var vs: seq<pVar> := seqVarsIn(e);
        result := [];
        var interp := all_false_interp(e);
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
    method all_false_interp(e: pExp) 
        returns (result: pInterpretation)
    {
        var vs := seqVarsIn(e);
    
        // start with an empty map
        result := map[];

        // iterate through variables in vs
        var i := 0;
        while (i < | vs |)
        {
            // for each one, add a maplet from it to false
            result := result[ vs[i] := false ];
            i := i + 1;
        }

        // that's it
        return result;
    }

    /*
    Takes a sequence of variables and an interpretation
    (meant to be) for those variables, and computes the
    "next" interpretation for those variables. It does this
    by in effect treating the sequence of values as a 
    binary integer and by incrementing it by one.
    */
    method next_interp(vs: seq<pVar>, interp: pInterpretation) 
        returns (result: pInterpretation)
    {
        result := interp;
        var i := | vs | - 1;
        while (i >= 0 ) 
        {
            // should be able to get rid of this with precondition
            if (! (vs[i] in interp)) { return; }
            assert vs[i] in interp;

            // The first time we find a 0, make it 1 and we're done
            if (interp[ vs[i] ] == false) 
            { 
                result := result[ vs[i] := true ];
                break; 
            } 
            else
            {
                result := result[ vs[i] := false ];
                // 1 + 1 = 0 plus a carry, so keep looping
            }

            i := i - 1;
        }
        return result;
    }

    function method pow2(n: nat): (r: nat)
        ensures r >= 1
    { 
        if n == 0 then 1 else 2 * pow2(n-1) 
    }
}