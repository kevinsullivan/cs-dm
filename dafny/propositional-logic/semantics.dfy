 include "interpretation.dfy"
 
 module semantics
 {
     import opened syntax
     import opened interpretation

    /*
    Evaluate a propositional expression given an interpretation.
    The recursive structure of this algorithm again reflects the
    inductive structure of the expressions defined by the syntax
    of our language.
    */
    function method pEval(e: pExp, i: pInterpretation): (r: bool)
    {
        match e 
        {
            // Evaluate constants (literals) to corresponding values
            case pTrue => true
            case pFalse => false

            // Evaluate variable expressions by lookup in environment
            case pVarExp(v: pVar) => pVarValue(v,i)

            // Evaluate operator exprs recursively in same environment
            case pNot(e1: pExp) => !pEval(e1,i)
            case pAnd(e1, e2) => pEval(e1,i) && pEval(e2, i)
            case pOr(e1, e2) =>  pEval(e1, i) || pEval(e2, i)
            case pImpl(e1, e2) => pEval(e1, i) ==> pEval(e2, i)
        }
    }    
 }