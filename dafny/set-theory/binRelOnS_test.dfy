/*
(c) Kevin Sullivan. 2018.
*/

include "binRelOnS.dfy"
include "binRelOnST.dfy"

module binRelOnS_test
{
    import opened binRelS
    import opened binRelST

    method Main()
    {
        /*
        Make a set and two binary relations over this set.
        We define the pair sets explicitly using display
        notation.
        */
        var aSet := { 1, 2, 3, 4, 5, 7, 9, 10 };
        var somePairs := {(1,5), (2,5), (3, 7), (4,7), (5, 10), (7, 10)};
        var otherPairs := { (2, 4), (3,9), (3, 4), (4, 1) };
        var aRel := new binRelOnS(aSet, somePairs);
        var otherRel := new binRelOnS(aSet, otherPairs);


        /*
        Print out relation, "aRel", then print its properties,
        and finally print out derived relations, including its
        composition with "otherRel".
        */
        print "\n\n*********** Relation R ***************\n\n";
        showRel("S", aRel); 
        analyzeRelation(aRel);
        deriveRelations(aRel,otherRel);

         /*
        Compute, print out, and print the properties of the
        reflexive, transitive closure of "aRel". 
        */
       print "\n\n***** Reflexive Transitive Closure of R ******\n\n";
        var rtc := aRel.reflexiveTransitiveClosure();
        showRel("S", rtc); 
        analyzeRelation(rtc);
    }

    /*
    Determine and print out the properties of relation, r.
    */
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
        showProp(r.isEquivalence(), "an equivalence relation");
        showProp(r.isPreorder(), "a preorder");
        showProp(r.isQuasiOrder(), "a Stanat & McAllister quasi-order");
        showProp(r.isWeakOrdering(), "a weak ordering");
        showProp(r.isPartialOrder(), "a partial order");
        showProp(r.isPrewellordering(), "a pre-well-ordering");
        showProp(r.isWellFounded(), "well founded");
        showProp(r.isTotalOrder(), "a total order");
        showProp(r.isStrictPartialOrder(), "a strict partial order");
        showProp(r.isStrictWeakOrdering(), "a strict weak ordering");
        showProp(r.isCoreflexive(), "coreflexive");
        showProp(r.isTrichotomous(), "trichotomous");
        showProp(r.isLeftEuclidean(), "left Euclidean");
        showProp(r.isRightEuclidean(), "right Euclidean");
        showProp(r.isEuclidean(), "Euclidean");
        showProp(r.isDependencyRelation(), "a dependency relatio");
    }

    
    /*
    Compute and print out derived relations
    */
    method deriveRelations<T>(r: binRelOnS<T>, s: binRelOnS<T>)
        requires r.Valid();     // shouldn't have to say this
        requires s.Valid();
        requires s.dom() == r.codom();
    {
        var compRel := r.composeS(s);
        var inverse := r.inverse();
        var reflexiveClosure := r.reflexiveClosure();
        var symmetricClosure := r.symmetricClosure();
        var transitiveClosure := r.transitiveClosure();
        var refTransClosure := r.reflexiveTransitiveClosure();
        var reflexiveReduction := r.reflexiveReduction();
        var rstc :=  r.reflexiveSymmetricTransitiveClosure();

        showRel("S o R", compRel); 
        showRel("inverse(R)", inverse); 
        showRel("reflexiveClosure(R)", reflexiveClosure); 
        showRel("symmetricClosure(R)", symmetricClosure); 
        showRel("transitiveClosure(R)", transitiveClosure); 
        showRel("reflexiveTransitiveClosure(R)", refTransClosure);
        showRel("reflexiveReduction(R)", reflexiveReduction); 
        showRel("reflexiveSymmetricTransitiveClosure(R)", rstc); 
        // showRel("transitiveReduction(R)", transitiveReduction); // TBD
        // show independencyRelationOnS

}

    method showProp(hasProp: bool, labl: string)
    {
        print "The relation ", isNt(hasProp), " ", labl, "\n";
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