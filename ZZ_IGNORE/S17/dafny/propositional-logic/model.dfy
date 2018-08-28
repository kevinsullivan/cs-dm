include "evaluation.dfy"
include "truth_table.dfy"

module model
{
    import opened syntax
    import opened interpretation
    import opened truth_table
    import opened evaluation
    import opened variables

    /*
    This important method returns a sequence 
    containing all (and only) the models of the
    given proposition. It works by generating a
    sequence of all possible interpretations for
    the variables in the proposition (this is the
    purpose of truth_table_inputs), and by then
    passing these interpretations, the proposition,
    and an empty list of models to the helper
    function, which augments that empty list with
    each of the interpretations for which the
    proposition evaluates to true.
    */
    method get_models(p: prop) returns 
        (r: seq<pInterpretation>)
    {
        var tt_inputs := truth_table_inputs_for_prop(p);
        r := get_models_helper (tt_inputs, p, []);
        return r;
        
    }

    /*
    This method iterates through a list of interpretations
    and appends each one, for which the given proposition, 
    e, evaluates to true, to the list, acc, which is then
    returned.
    */
   method get_models_helper(tt_inputs: seq<pInterpretation>, p: prop, acc: seq<pInterpretation>) 
        returns (r: seq<pInterpretation>)
        requires forall v :: v in getVarsInProp(p) ==> 
                    forall i :: 0 <= i < |tt_inputs| ==> 
                        v in tt_inputs[i];  // kjs -- need to import variables
    {
        var idx := 0;
        var res := acc;
        while (idx < | tt_inputs |)
        {
            if pEval(p, tt_inputs[idx]) 
            { res := res + [ tt_inputs[idx] ]; } 
            idx := idx + 1;
        }
        return res;
    }
}