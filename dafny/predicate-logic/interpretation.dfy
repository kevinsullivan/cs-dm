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

    We define a "type synonym," pInterpretation, short
    for "propositional logic interpretation", for the
    map<bVar,bool> type. Type synonyms don't change the 
    behavior of code. Rather, they serve to document 
    the purpose of the code for human readers. In this 
    sense, they support a form of "abstraction", hiding 
    complex details behind a simpler, meaningful name.
    pInterpreation means exactly map<propVar, bool>.
    */
    type pInterpretation = map<propVar, bool>

 
    /*
    This method returns the value assigned to a given
    propositional variable by a given interpretation.
    This function can only be called with a variable, v,
    for which the given interpretation, i, has a value.
    However, this pre-condition is not formalized or
    enforced.
    */
    function method pVarValue(v: propVar, i: pInterpretation): bool
        requires v in i
    {
        i[v]
    }

    /*
    This method serializes an interpretation to a string,
    using the string name of each variable in the output.
    */
    method show_interpretation (interp: pInterpretation, vs: seq<propVar>,labels: bool)
        requires forall v :: v in vs ==> v in interp
    {
        var n := | vs |;
        var i := 0;
        print "[";
        while (i < n) {
            if vs[i] in interp 
            {
                if labels { print vs[i].name, " := "; }
                print interp[vs[i]];
                if (i < n - 1) { print "\t"; }
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
method show_interpretations(interps: seq<pInterpretation>, vs: seq<propVar>, labels: bool)
    requires forall i :: 0 <= i < |interps| ==> 
        (forall v :: v in vs ==> v in interps[i])
{
    var i := 0;
    print "{\n";
    while (i < |interps|)
        {
            show_interpretation(interps[i], vs, labels);
            if i < |interps| - 1 { print ",\n"; }
            i := i + 1;
        }
     print "\n}\n";
    }
 }

 