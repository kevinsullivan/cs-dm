module myblang
{
    // SYNTAX: Expresions are just values!
    datatype bExp = 
        bTrue | 
        bFalse | 
        bNot(e: bExp) |
        bAnd(e1: bExp, e2: bExp)

    // SEMANTICS: From expressions to meanings.
    function method bEval(e: bExp): bool    
    {
        match e 
        {
            case bTrue => true 
            case bFalse => false
            case bAnd(e1, e2) => bEval(e1) && bEval(e2)
            case bNot(e) => !bEval(e)
        }
    }

    
    // Evaluating expressions in practice.
    method Main()
    {
        print bEval(bTrue), "\n";
        print bEval(bFalse), "\n";
        print bEval(bNot(bAnd(bTrue,bFalse))), "\n";
        var myFirstBExp := bNot(bAnd(bTrue,bFalse));
        print bEval(myFirstBExp);
    }
}