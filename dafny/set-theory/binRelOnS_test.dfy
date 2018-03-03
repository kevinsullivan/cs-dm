include "binRelOnS.dfy"
include "binRelOnST.dfy"

module binRelOnS_test
{
    import opened binRelS
    import opened binRelST

    method Main()
    {
        var s := { 1, 2, 3, 4, 9 };
        var p := { (1,1), (2,3) };
        var q := { (1,4), (3,9) };

        var rs := new binRelOnS(s, p);
        var qs := new binRelOnS(s, q);
        var h := composeSS(qs, rs);
        print "The composition is ", h.rel(), "\n";

        var rst := new binRelOnST(s,s,p);

        print "rst(3) = ", rst.image(3), "\n";
        print "rs(3) = ", rs.image(3), "\n";

        if (rst.isFunction() && rst.isDefinedFor(3))
        {
            var x1 := rst.fimage(3);       
            print "rst(3) = ", x1, "\n";
        }

        analyzeRelation(rs);
    }

    method analyzeRelation<T>(r: binRelOnS<T>)
        requires r.Valid();     // shouldn't have to say this
    {
        var t := r.isTotal();
        var isFun := r.isFunction();
        var s := if isFun then r.isSurjective() else false;
        var p := r.isPartial();
        var i := if isFun then r.isInjective() else false;
        var f := r.isFunction();
        var b := if isFun then r.isBijective() else false;
        var x := r.isReflexive();
        var y := r.isSymmetric();
        var v := r.isTransitive();
        print "R ", isNt(t), " total\n";
        print "R ", isNt(p), " partial\n";
        print "R ", isNt(f), " a function\n";
        print "R ", isNt(s), " surjective\n";
        print "R ", isNt(i), " injective\n";
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