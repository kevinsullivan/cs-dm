 include "interpretation.dfy"
 
 module evaluation
 {
     import opened expression
     import opened interpretation

    /*
    Evaluate a Boolean expression in a given environment. 
    The recursive structure of this algorithm reflects the
    inductive structure of the expressions we've defined.
    */
    function method Beval(e: Bexp, i: Binterp): (r: bool) 
    {
        match e 
        {
            // Evaluate literal expressions to corresponding values
            case litExp(b: bool) => b
        
            // Evaluate variable expressions by lookup in environment
            case varExp(v: Bvar) => lookup(v,i)

            // Evaluate operator exprs recursively in same environment
            case notExp(e1: Bexp) => !Beval(e1,i)
            case andExp(e1, e2) => Beval(e1,i) && Beval(e2, i)
            case orExp(e1, e2) =>  Beval(e1, i) || Beval(e2, i)
        }
    }    
 }