include "evaluation.dfy"

module bool_satisfiability
{
    import opened expression
    import opened interpretation
    import opened evaluation


    method satisfiable(e: pExp) 
        returns (result: bool, model: pInterp)
    {
        var vars := seqVarsIn(e);
        var interps := all_interps(vars);
        var i := 0;
        while (i < | interps |) 
        {
            if (pEval(e,interps[i])) 
            { 
                result := true;
                model := interps[i];
                return;
            }
            i := i + 1;        
        }
        return false, map[];
    }

    /*
    Return true (and an empty interpretation) if e is unsatisfiable,
    otherwise return false and a counterexample, i.e., a model, i.e.,
    an interpretation, that makes the expression true.
    */
    method unsatisfiable(e: pExp) 
        returns (sat: bool, counterexample: pInterp)
    {
        var model: Binterp;
        sat, model := satisfiable(e);
        counterexample := model;        // for understandability
        return !sat, counterexample;
    }

    /*
    Return true (and an empty interpretation) if the given
    Boolean expression is valid, otherwise return false and
    a counter-example, i.e., an interpretation for which the
    given expression is false
    */
    method valid(e: pExp) 
        returns (result: bool, counterexample: pInterp)
    {
        var vars := seqVarsIn(e);
        var interps := all_interps(vars);
        var i := 0;
        while (i < | interps |) 
        {
            if (!pEval(e,interps[i])) 
            { 
                result := false;
                counterexample := interps[i];
                return;
            }
            i := i + 1;        
        }
        return true, map[];
    }
}