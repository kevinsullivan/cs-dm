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
        showRelation("S", aRel); 
        showProperties(aRel);
        showDerivedRelations(aRel,otherRel);

        /*
        As an illustration of capabilities of this code, 
        compute, print out, and print the properties of the
        reflexive transitive closure of "aRel". 
        */
        print "\n\n***** Reflexive Transitive Closure of R ******\n\n";
        var rtc := aRel.reflexiveTransitiveClosure();
        showRelation("S", rtc); 
        showProperties(rtc);
    }

    /*
    Determine and print out the properties of relation, r.
    */
    method showProperties<T>(r: binRelOnS<T>)
        requires r.Valid();     // shouldn't have to say this
    {
        print "\n\nFUNCTION PROPERTIES\n";
        showProp(r.isFunction(), "a function");
        if r.isFunction()
        {
            showProp(r.isSurjective(), "surjective");
            showProp(r.isInjective(), "injective");
            showProp(r.isBijective(), "bijective");
        }
        showProp(r.isTotalFunction(), "a total function");
        showProp(r.isPartialFunction(), "a partial function");

        print "\n\nBASIC PROPERTIES OF BINARY RELATIONS\n";
        showProp(r.isReflexive(), "reflexive");
        showProp(r.isSymmetric(), "symmetric");
        showProp(r.isTransitive(), "transitive");
        showProp(r.isEquivalence(), "an equivalence relation");

        print "\n\nMORE PROPERTIES OF BINARY RELATIONS\n";
        showProp(r.isTotal(), "a total (complete) relation");
        showProp(r.isIrreflexive(), "irreflexive"); 
        showProp(r.isAntisymmetric(), "antisymmetric");
        showProp(r.isAsymmetric(), "asymmetric");
        showProp(r.isQuasiReflexive(), "quasi-reflexive");
        showProp(r.isCoreflexive(), "coreflexive");

        print "\n\nBASIC ORDER THEORY PROPERTIES\n";
        showProp(r.isPreorder(), "a preorder");
        showProp(r.isPartialOrder(), "a partial order");
        showProp(r.isTotalOrder(), "a total order");

        print "\n\nMORE ADVANCED ORDER THEORY PROPERTIES\n";
        showProp(r.isTotalPreorder(), "a total preorder");
        showProp(r.isQuasiOrder(), "a Stanat & McAllister quasi-order");
        showProp(r.isWeakOrdering(), "a weak ordering");
        showProp(r.isStrictPartialOrder(), "a strict partial order");
        showProp(r.isStrictWeakOrdering(), "a strict weak ordering");
        showProp(r.isWellFounded(), "well founded");
        showProp(r.isPrewellordering(), "a pre-well-ordering");

        print "\n\nOTHER PROPERTIES OF BINARY RELATIONS\n";
        showProp(r.isTrichotomous(), "trichotomous");
        showProp(r.isLeftEuclidean(), "left Euclidean");
        showProp(r.isRightEuclidean(), "right Euclidean");
        showProp(r.isEuclidean(), "Euclidean");
        showProp(r.isDependencyRelation(), "a dependency relation");
    }

    
    /*
    Compute and print out derived relations
    */
    method showDerivedRelations<T>(r: binRelOnS<T>, s: binRelOnS<T>)
        requires r.Valid();     // shouldn't have to say this
        requires s.Valid();
        requires s.dom() == r.codom();
    {
        var compRel := r.compose(s);
        var inverse := r.inverse();
        var reflexiveClosure := r.reflexiveClosure();
        var symmetricClosure := r.symmetricClosure();
        var transitiveClosure := r.transitiveClosure();
        var refTransClosure := r.reflexiveTransitiveClosure();
        var reflexiveReduction := r.reflexiveReduction();
        var rstc :=  r.reflexiveSymmetricTransitiveClosure();

        showRelation("S o R", compRel); 
        showRelation("inverse(R)", inverse); 
        showRelation("reflexiveClosure(R)", reflexiveClosure); 
        showRelation("symmetricClosure(R)", symmetricClosure); 
        showRelation("transitiveClosure(R)", transitiveClosure); 
        showRelation("reflexiveTransitiveClosure(R)", refTransClosure);
        showRelation("reflexiveReduction(R)", reflexiveReduction); 
        showRelation("reflexiveSymmetricTransitiveClosure(R)", rstc); 
        // showRelation("transitiveReduction(R)", transitiveReduction);
        // show independencyRelationOnS // TBD
}

    method showProp(hasProp: bool, labl: string)
    {
        print "The relation ", isNt(hasProp), " ", labl, "\n";
    }

    function method isNt(b: bool): string
    {
        if b then "is" else "isn't"
    }

    method showRelation<T>(labl: string, r: binRelOnS<T>) 
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