include "binRelOnS.dfy"

module binRelOnS_test
{
    import opened binRelS

       method Main()
    {
        var s := { 1, 2, 3 };
        var p := {(1,1), (2,2), (3,3), (3,2) };
        var r := new binRelOnS(s, p);
        analyzeRelation(r);
    }

    method analyzeRelation<T>(r: binRelOnS<T>)
        requires r.Valid();     // shouldn't have to say this
    {
        var t := r.isTotal();
        var s := r.isSurjective();
        var p := r.isPartial();
        var i := r.isInjective();
        var f := r.isFunction();
        var b := r.isBijective();
        var x := r.isReflexive();
        var y := r.isSymmetric();
        var v := r.isTransitive();
        print "R ", isNt(t), " total\n";
        print "R ", isNt(s), " surjective\n";
        print "R ", isNt(p), " partial\n";
        print "R ", isNt(i), " injective\n";
        print "R ", isNt(f), " a function\n";
        print "R ", isNt(b), " bijective\n";
        print "R ", isNt(x), " reflexive\n";
        print "R ", isNt(y), " symmetric\n";
        print "R ", isNt(v), " transitive\n";
    }

    function method isNt(b: bool): string
    {
        if b then "is" else "isn't"
    }
}