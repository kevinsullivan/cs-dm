include "evaluation.dfy"
include "truth_table.dfy"

module model
{
    import opened syntax
    import opened interpretation
    import opened truth_table
    import opened evaluation


    method get_models(e: pExp) returns 
        (r: seq<pInterpretation>)
    {
        var tt_inputs := truth_table_inputs(e);
        r := get_models_helper (tt_inputs, e, []);
        return r;
        
    }

   method get_models_helper(tt_inputs: seq<pInterpretation>, e: pExp, acc: seq<pInterpretation>) 
        returns (r: seq<pInterpretation>)
    {
        var idx := 0;
        var res := acc;
        while (idx < | tt_inputs |)
        {
            if pEval(e, tt_inputs[idx]) 
            { res := res + [ tt_inputs[idx] ]; } 
            idx := idx + 1;
        }
        return res;
    }
}