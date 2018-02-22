module expression
{
    /*
        Now we define the *syntax* of a little language 
        of Boolean expressions.
    */

    /*
    We use the definition of the syntax of Boolean expressions
    to introduce the fundamental concept of inductive definitions.
    Inductive definitions of data types representing often infinite 
    sets of values is done by first defining a set starting values
    (like base cases for a recursion) and then by defining rules for 
    forming new values from ones already defined. 
    */


    /*
    Here the base values are the terms litTrue and litFalse. We 
    will eventually interpret them as "literal" terms representing
    the Boolean values, true and false.
    */
    datatype bExp = 
        bTrue |
        bFalse | 
        bNot (e: bExp) |
        bAnd (e1: bExp, e2: bExp) |
        bOr (e1: bExp, e2: bExp)


    /*
    A method to convert a bExp to a string. This method uses 
    the  fundamental concept of "destructuring" a value of an
    inductively defined type by matching the value against the
    constructor used to create it, extracting the arguments 
    that were passed to the constructor, and then recursively 
    printing subparts until the base cases are reached.
    */

    function method show_bExp(e: bExp): string
    {
        match e 
        {
            case bTrue => "True"
            case bFalse => "False"
            case bNot (e: bExp) => 
                "NOT (" + show_bExp(e) + ")"
            case bAnd (e1: bExp, e2: bExp) => 
                "AND (" + show_bExp(e1) + ", " + show_bExp(e2) + ")"
            case bOr (e1: bExp, e2: bExp) =>  
                "OR (" + show_bExp(e1) + ", " + show_bExp(e2) + ")"
            
        }
    }

       function method show_bExp_infix(e: bExp): string
    {
        match e 
        {
            case bTrue => "True"
            case bFalse => "False"
            case bNot (e: bExp) => 
                "(Not " + show_bExp_infix(e) + ")"
            case bAnd (e1: bExp, e2: bExp) => 
                "(" + show_bExp_infix(e1) + " AND " + show_bExp_infix(e2) + ")"
            case bOr (e1: bExp, e2: bExp) =>  
                "(" + show_bExp_infix(e1) + " OR " + show_bExp_infix(e2) + ")"
            
        }
    }

}