include "binRelOnS.dfy"
include "binRelOnST.dfy"

module binRelOnS_test
{
    import opened binRelS
    import opened binRelST

    method Main()
    {
        /*
        Make a set and two binary relations over this set
        */
        var aSet := { 1, 2, 3, 4, 9 };
        var somePairs := { (1,2), (2,3), (3, 4), (4,9) };
        var otherPairs := { (2, 4), (3,9), (3, 4), (4, 1) };
        var aRel := new binRelOnS(aSet, somePairs);
        var otherRel := new binRelOnS(aSet, otherPairs);

        /*
        Compute some derived relations
        */
        var compRel := aRel.composeS(otherRel);
        var inverse := aRel.inverse();
        var reflexiveClosure := aRel.reflexiveClosure();
        var symmetricClosure := aRel.symmetricClosure();
        var transitiveClosure := aRel.transitiveClosure();
        var refTransClosure := aRel.reflexiveTransitiveClosure();
        var reflexiveReduction := aRel.reflexiveReduction();
        //var transitiveReduction := aRel.transitiveReduction();  // TBD


        showRel("R", aRel); 

        analyzeRelation(aRel);

        showRel("S", otherRel); 
        showRel("S o R", compRel); 
        showRel("inverse(R)", inverse); 
        showRel("transitiveClosure(R)", transitiveClosure); 
        showRel("reflexiveClosure(R)", reflexiveClosure); 
        showRel("symmetricClosure(R)", symmetricClosure); 
        showRel("reflexiveReduction(R)", reflexiveReduction); 
    }

    method analyzeRelation<T>(r: binRelOnS<T>)
        requires r.Valid();     // shouldn't have to say this
    {
        showProp(r.isFunction(), "a function");
        if r.isFunction()
        {
            showProp(r.isSurjective(), "surjective");
            showProp(r.isInjective(), "injective");
            showProp(r.isBijective(), "bijective");
        }
        showProp(r.isTotal(), "total");
        showProp(r.isPartial(), "partial");
        showProp(r.isReflexive(), "reflexive");
        showProp(r.isQuasiReflexive(), "quasi-reflexive");
        showProp(r.isIrreflexive(), "irreflexive"); // aka anti-reflexive
        showProp(r.isSymmetric(), "symmetric");
        showProp(r.isAntisymmetric(), "antisymmetric");
        showProp(r.isAsymmetric(), "asymmetric");
        showProp(r.isTransitive(), "transitive");
        showProp(r.isEquivalence(), "equivalence");
        showProp(r.isPreorder(), "preorder");
        showProp(r.isWeakOrdering(), "a weak ordering");
        showProp(r.isPartialOrder(), "a partial order");
        showProp(r.isPrewellordering(), "a pre-well-ordering");
        showProp(r.isWellFounded(), "well founded");
        showProp(r.isTotalOrder(), "a total order");
    }

    method showProp(hasProp: bool, labl: string)
    {

    }

    function method isNt(b: bool): string
    {
        if b then "is" else "isn't"
    }

    method showRel<T>(labl: string, r: binRelOnS<T>) 
        requires r.Valid();
        ensures r.Valid();
    {
        print labl; 
        show(r); 
        print "\n";
    }

    
    
    /*
    Show -- return a string representation of relation in
    "dot" format. Current just shows pairs in rel() and does
    not show domain or co-domain elements not mapped.
    */
    method show<T>(r: binRelOnS<T>) 
        requires r.Valid();
        ensures r.Valid();
    {
        print "\ndigraph\n{\n";
        var p := r.rel();
        while (p != {})
            decreases p;
        {
            var e :| e in p;
            var d := e.0;
            var c := e.1;
            print d, " -> ", c, ";\n";
            p := p - { e };
        }
        print "}";
    }
}