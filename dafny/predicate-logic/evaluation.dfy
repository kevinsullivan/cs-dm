 include "interpretation.dfy"
 include "variables.dfy"
 
 module evaluation
 {
     import opened syntax
     import opened interpretation
     import opened variables

    /*
    Evaluate a propositional expression given an interpretation,
    yielding a Dafny Boolean values as a result. The recursive 
    structure of this code mirrors the inductive definition of 
    the syntax of expressions in propositional logic. 
    */
    function method pEval(e: prop, i: pInterpretation): (r: bool)
        requires forall v :: v in getVarsInProp(e) ==> v in i
    {
        match e 
        {
            case pTrue => true
            case pFalse => false
            case pVar(v: propVar) => pVarValue(v,i)
            case pNot(e1: prop) => !pEval(e1,i)
            case pAnd(e1, e2) => pEval(e1,i) && pEval(e2, i)
            case pOr(e1, e2) =>  pEval(e1, i) || pEval(e2, i)
            case pImpl(e1, e2) => pEval(e1, i) ==> pEval(e2, i)
        }
    }    
 }