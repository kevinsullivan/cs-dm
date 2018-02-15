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
}