 include "syntax.dfy"
 
 module evaluation
 {
     import opened expression

    /*
    Evaluate a Boolean expression. The recursive structure 
    of this algorithm reflects the inductive structure of the 
    expressions we've defined.
    */
    function method bEval(e: bExp): bool
    {
        match e 
        {
            // Evaluate literal expressions to corresponding values
            case bTrue => true
            case bFalse => false
        
            // Evaluate operator exprs recursively 
            case bNot(e: bExp) => !bEval(e)
            case bAnd(e1, e2) => bEval(e1) && bEval(e2)
            case bOr(e1, e2) =>  bEval(e1) || bEval(e2)
            case bImpl(e1, e2) => bEval(e1) ==> bEval(e2)
        }
    }    
 }