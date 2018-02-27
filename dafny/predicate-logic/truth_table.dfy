include "interpretation.dfy"
include "variables.dfy"
include "evaluation.dfy"

module truth_table
{
    import opened syntax
    import opened variables
    import opened interpretation
    import opened evaluation

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
    method truth_table_inputs_for_vars(vs: seq<propVar>) 
        returns (result: seq<pInterpretation>)
    {
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
    
    method truth_table_inputs_for_prop(p: prop) 
        returns (result: seq<pInterpretation>)
    {
        var vs := seqVarsInProp(p);
        result := truth_table_inputs_for_vars(vs);
        return;
    }
    
    method truth_table_inputs_for_props(ps: seq<prop>) 
        returns (result: seq<pInterpretation>)
    {
        var vs := seqVarsInProps(ps);
        result := truth_table_inputs_for_vars(vs);
        return;
    }
    
     /*
        Return an interpretation for the variables in 
        the sequence vs such that every variable maps 
        to false.
    */
    method all_false_interp(vs: seq<propVar>) 
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
    method next_interp(vs: seq<propVar>, interp: pInterpretation) 
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

    method show_truth_table_for_prop(p: prop, ord: seq<propVar>, labels: bool)
        // assume var_order complete for props; would be better to check
    {
        var varSeq := seqVarsInProp(p);
        var tt_inputs := truth_table_inputs_for_vars(varSeq);
        var i := 0;
        while (i < | tt_inputs |) 
        {
            show_interpretation(tt_inputs[i],ord,labels);
            print " :: ";
            var out := pEval(p, tt_inputs[i]);
            var propString := showProp(p);
            if labels { print propString, " := "; }
            print out, "\n";
            i := i + 1;
        } 
    }
}