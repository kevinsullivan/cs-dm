 include "syntax.dfy"

 module interpretation
 {
    import opened syntax

   /*
    An "interpretation" maps propositional variables
    to Boolean values. We represent an interpretation 
    as a Dafny map from pVar values to to Dafny bools:
    i.e., map<bVar,bool>. 
    
    When we need to evaluate a variable expression, 
    we'll  look up the value of the variable in such
    a map. 

    We define a "type synonym," pInterpretation, for 
    map<bVar,bool>. Type synonyms don't change the 
    behavior of code. Rather, they serve to document 
    the purpose of the code for human readers. In this 
    sense, they support a form of "abstraction", hiding 
    complex details behind a simpler, meaningful name.
    */

    type pInterpretation = map<pVar, bool>

 
    /*
    This method returns the value assigned to a given
    propositional variable by a given interpretation,
    or false if the variable's not mapped by it. The
    design of this code would be improved by the
    addition of a precondition that requires v in i.
    */
    function method pVarValue(v: pVar, i: pInterpretation): bool
    {
        if (v in i) then i[v] else false
    }


    /*
    This method serializes an interpretation to a string,
    using the string name of each variable in the output.
    The design would be improved by a pre-condition that
    requires forall v :: v in vs ==> v in interp.
    */
    method show_pInterp(interp: pInterpretation, vs: seq<pVar>)
    {
        var n := | vs |;
        var i := 0;
        print "[";
        while (i < n) {
            if vs[i] in interp 
            {
                print vs[i].name, " := ", interp[vs[i]], ", ";
            }
            i := i + 1;
        }
        print "]";
    }
 
 /*
 This method serializes a sequence of interpretations,
 using the preceding method to serialize each one, and 
 is mainly used to output, for example, lists of models 
 or counterexamples of given propositions.
 */
 method show_pInterps(interps: seq<pInterpretation>, vs: seq<pVar>)
    {
        var i := 0;
        print "{\n";
        while (i < |interps|)
        {
            show_pInterp(interps[i], vs);
            if i < |interps| - 1 { print ",\n"; }
            i := i + 1;
        }
        print "\n}\n";
    }
 }

 