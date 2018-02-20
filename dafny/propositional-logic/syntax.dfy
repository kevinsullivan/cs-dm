include "syntax.dfy"

module syntax
{
    datatype propVar = mkPropVar(name: string) 

   /*
   A value of this prop type represents a sentence, 
   or expression, in propositional logic. Such an
   expression is a constant (pTrue or pFalse); a 
   propositional variable (here, represented by a
   value of type pVar); or an expression created by 
   applying one of the logical connectives to one 
   or more smaller propositions. A value of this
   type is structured as what we call an "abstract
   syntax tree."
   */
    datatype prop = 
        pTrue | 
        pFalse |
        pVar (v: propVar) |
        pNot (e: prop) |
        pAnd (e1: prop, e2: prop) |
        pOr (e1: prop, e2: prop) |
        pImpl (e1: prop, e2: prop)


    /*
    showprop takes a propositional expression in
    the form of a prop value (an abstract syntax
    tree) and serializes it into a string using
    prefix notation for the operator/connectives.
    The propositional constants are translated to
    the strings, "pTrue" and "pFalse" to avoid 
    any confusion with the Boolean values true
    and false, which Dafny prints as the strings,
    "True" and "False".
    */
    method showProp(e: prop) returns (f: string) 
        decreases e
    {
        match e {
            case pTrue => return "pTrue";
            case pFalse => return "pFalse";
            case pVar(s) => return s.name;
            case pNot(e') =>
            {
                var s:= showProp(e');
                return "Not(" +  s + ")"; 
            }
            case pAnd(e1,e2) => 
            {
                var s1:= showProp(e1);
                var s2:= showProp(e2);
                return "And(" + s1 + ", " + s2 + ")";
            }
            case pOr(e1,e2) => 
            {
                var s1:= showProp(e1);
                var s2:= showProp(e2);
                return "Or(" + s1 + ", " + s2 + ")";
            }
            case pImpl(e1,e2) => 
            {
                var s1:= showProp(e1);
                var s2:= showProp(e2);
                return "Implies(" + s1 + ", " + s2 + ")";
            }
        }
    }
}