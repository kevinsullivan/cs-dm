module syntax
{
    /*
    This module implements the syntax of 
    propositional logic, with the data type,
    pVar, representing propositional variables,
    and pExp, propositional expressions: i.e.,
    "propositions".
    
    We start by defining an infinite set of 
    "propositional variables" as terms of the 
    form mkVar(s), and of type, pVar. When a 
    pVar is created, the string, prop, be used 
    to express a real-world truth claim, such 
    as  "Joe is from Montana", or it can be an 
    abstract name, such as "P". 
    */

    datatype pVar = mkPVar(name: string) 

   /*
   A value of this pExp type represents a sentence, 
   or expression, in propositional logic. Such an
   expression is a constant (pTrue or pFalse); a 
   propositional variable (here, represented by a
   value of type pVar); or an expression created by 
   applying one of the logical connectives to one 
   or more smaller propositions. A value of this
   type is structured as what we call an "abstract
   syntax tree."
   */
    datatype pExp = 
        pTrue | 
        pFalse |
        pVarExp (v: pVar) |
        pNot (e: pExp) |
        pAnd (e1: pExp, e2: pExp) |
        pOr (e1: pExp, e2: pExp) |
        pImpl (e1: pExp, e2: pExp)


    /*
    showPExp takes a propositional expression in
    the form of a pExp value (an abstract syntax
    tree) and serializes it into a string using
    prefix notation for the operator/connectives.
    The propositional constants are translated to
    the strings, "pTrue" and "pFalse" to avoid 
    any confusion with the Boolean values true
    and false, which Dafny prints as the strings,
    "True" and "False".
    */
    method showPExp(e: pExp) returns (f: string) 
        decreases e
    {
        match e {
            case pTrue => return "pTrue";
            case pFalse => return "pFalse";
            case pVarExp(s) => return s.name;
            case pNot(e') =>
            {
                var s:= showPExp(e');
                return "Not(" +  s + ")"; 
            }
            case pAnd(e1,e2) => 
            {
                var s1:= showPExp(e1);
                var s2:= showPExp(e2);
                return "And(" + s1 + ", " + s2 + ")";
            }
            case pOr(e1,e2) => 
            {
                var s1:= showPExp(e1);
                var s2:= showPExp(e2);
                return "Or(" + s1 + ", " + s2 + ")";
            }
            case pImpl(e1,e2) => 
            {
                var s1:= showPExp(e1);
                var s2:= showPExp(e2);
                return "Implies(" + s1 + ", " + s2 + ")";
            }
        }
    }
}