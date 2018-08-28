 include "syntax.dfy"
 
 module evaluation
 {
     import opened expression

    /*
    While the *syntax* of a language defines the form of legal
    expressions in the language, the *semantics* of a language
    specify the *meaning* of each such legal expression. In our
    case of Boolean expressions, the meaning of an expression 
    is simply a Boolean value, either true or false. 
    
    In other words, to every expression in our language there 
    is a corresponding single Boolean value that expresses the
    meaning of the expressions. 
    
    We can thus formalize the semantics of our language as a 
    *function* from expressions (which are just values of our
    bExp type, after all) to bool! Given an expression, our
    function, bEval, *evaluates* it, which is to say that it
    determines, and then returns, its meaning. 
    
    When given a literal expressions, pTrue or pFalse, bEval
    simply returns true or false, respectively. For expressions
    built from subexpressions, bEval recursively evaluates the
    subexpressions and then applies a Boolean function to the
    result(s) depending on which constructor, corresponding to
    a connective, was used to build the expression. 
    */
    function method bEval(e: bExp): bool
    {
        match e 
        {
            // Literal expressions evaluate to base values
            case bTrue => true
            case bFalse => false
        
            // Operator expressions are evaluated recursively
            case bNot(e: bExp) => !bEval(e)
            case bAnd(e1, e2) => bEval(e1) && bEval(e2)
            case bOr(e1, e2) =>  bEval(e1) || bEval(e2)
            case bImpl(e1, e2) => bEval(e1) ==> bEval(e2)
        }
    }    
 }