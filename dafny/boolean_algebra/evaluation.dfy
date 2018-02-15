 include "expression.dfy"
 
 module evaluation
 {
     import opened expression

    /*
    Evaluate a Boolean expression in a given environment. 
    The recursive structure of this algorithm reflects the
    inductive structure of the expressions we've defined.
    */
    function method bEval(e: bExp): bool
    {
        match e 
        {
            // Evaluate literal expressions to corresponding values
            case bTrue => true
            case bFalse => false
        
            // Evaluate operator exprs recursively in same environment
            case bNot(e: bExp) => !bEval(e)
            case bAnd(e1, e2) => bEval(e1) && bEval(e2)
            case bOr(e1, e2) =>  bEval(e1) || bEval(e2)
        }
    }    
 }