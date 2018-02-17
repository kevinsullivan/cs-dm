include "model.dfy"

module decision
{  
    import opened syntax
    import opened interpretation
    import opened model
    /*
    Return true (and an empty interpretation) if the given
    Boolean expression is valid, otherwise return false with
    a counter-example, i.e., an interpretation for which the
    given expression is false
    */
    method satisfiable(e: prop) returns (result: bool, 
                                         models: seq<pInterpretation>)
    {
        models := get_models(e);
        if | models | > 0 { return true, models; }
        return false, [];
    }

    method valid(e: prop) returns (result: bool, 
                                   counters: seq<pInterpretation>)
    {
        var negIsSat: bool; 
        negIsSat, counters := satisfiable(pNot(e));
        return !negIsSat, counters;
    }
 
    /*
    Return true (and an empty interpretation) if e is unsatisfiable,
    otherwise return false and a counterexample, i.e., a model, i.e.,
    an interpretation, that makes the expression true.
    */
    method unsatisfiable(e: prop) 
        returns (result: bool, 
                 counters: seq<pInterpretation>)
    {
        var hasModels: bool;
        hasModels, counters := satisfiable(e);
        return !hasModels, counters;
    }
}
