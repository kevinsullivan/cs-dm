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

    /*
    A proposition is valid if it's true under every
    interpretation. If it's not valid, then there will
    be some interpretation under which it's false. In
    this case, the negation of the proposition will be
    true under that interpretation, and it will thus be
    a counterexample to the claim that the proposition 
    is valid. If such a "witness" to the invalidity of
    the original proposition is found, return false to
    the question of validity, along with the witnesses
    to invalidity.
    */
    method valid(e: prop) returns (result: bool, 
                                   counters: seq<pInterpretation>)
    {
        var negIsSat: bool; 
        negIsSat, counters := satisfiable(pNot(e));
        return !negIsSat, counters;
    }
 
    /*
    Invalidity means there's a witness to the negation 
    of the main propositions, i.e., that the negation 
    is satisfiable. Try to satisfy it and return results
    and counterexamples (models of the negated prop) 
    accordingly.

    */
    method invalid(e: prop) returns (result: bool, 
                             counters: seq<pInterpretation>)
    {
        var negIsSat: bool; 
        negIsSat, counters := satisfiable(pNot(e));
        return negIsSat, counters;
    }
 }
