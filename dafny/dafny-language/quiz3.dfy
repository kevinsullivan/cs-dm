module quiz3
{
    method quiz3()
    {
        var S1 := set s | 0 <= s <= 50 :: 2 * s;
        print S1, "\n";

        var T1 := set t | t in S1 && t < 25;
        print T1, "\n";

        var Q := set s, t | s in S1 && t in T1 :: (s, t);
        print Q, "\n";

        print | Q |, "\n";

        var S2 := S1 - T1;
        print S2, "\n";

        var S := { 1, 2, 3 };
        var P := set R | R <= S;
        print P;
    }

    function method set_product<T1,T2>(s1: set<T1>, s2: set<T2>): set<(T1,T2)>
    {
        set q, r | q in s1 && r in s2 :: (q,r)
    }

    /*
    A type of binary relation over a given
    set S. I.e., a set of ordered pairs, the
    individual elements of which are in S. 
    This type is not to be instantiated by
    end-programmers directly. Rather, the rel
    function should be used. It's sole purpose
    however is just to enforce the constraint. 
    */
    type relationS<T> = (set<T>,set<(T,T)>)

    /*
    */
    function method relS<T(!new)>(dom: set<T>, pairs: set<(T,T)>): 
        relationS<T> 
        requires forall x, y :: 
            (x, y) in pairs ==> x in dom && y in dom
    {
        (dom, pairs)
    }

    function method domS<T>(r: relationS<T>): set<T>
    {
        r.0
    }

    function method pairsS<T>(r: relationS<T>): set<(T,T)>
    {
        r.1
    }

    function method isTotalS<T(!new)>(r: relationS<T>): bool
        ensures isTotalS(r) ==> 
                  (forall x :: x in domS(r) ==> 
                    (exists y :: y in domS(r) && (x,y) in pairsS(r)))
    {
        (set x, y | x in domS(r) && y in domS(r) && (x, y) in pairsS(r) :: x) == domS(r)
    }

    function method isSurjectiveS<T>(r: relationS<T>): bool
    {
        (set x, y | x in domS(r) && y in domS(r) && (x, y) in pairsS(r) :: y) == domS(r)    
    }

    function method isPartialS<T>(r: relationS<T>): bool
    {
        !isTotalS(r)
    }

    function method isInjectiveS<T>(r: relationS<T>): bool
    {
      forall x, y, z :: x in domS(r) && y in domS(r) && z in domS(r) &&
                        (x, z) in pairsS(r) && 
                        (y, z) in pairsS(r) ==> 
                        x == y  
    }

    function method isFunctionS<T>(r: relationS<T>): bool
    {
      forall x, y, z :: x in domS(r) && y in domS(r) && z in domS(r) &&
                        (x, y) in pairsS(r) && 
                        (x, z) in pairsS(r) ==> 
                        y == z  
    }

    function method isBijectiveS<T>(r: relationS<T>): bool
    {
        isInjectiveS(r) && isSurjectiveS(r)    
    }

    function method isReflexiveS<T>(r: relationS<T>): bool
    {
        forall x :: x in domS(r) ==> (x, x) in pairsS(r) 
    }

    function method isSymmetricS<T>(r: relationS<T>): bool
    {
        forall x, y ::  x in domS(r) && y in domS(r) &&
                        (x, y) in pairsS(r) ==> (y, x) in pairsS(r)
    }

    function method isTransitiveS<T>(r: relationS<T>): bool
    {
        forall x, y, z ::  x in domS(r) && y in domS(r) && z in domS(r) &&
                          (x, y) in pairsS(r) && 
                          (y, z) in pairsS(r) ==> 
                          (x, z) in pairsS(r) 
    }

    /*
    method theX<T>(r: relationS<T>, x: T) returns (ret: T)
        requires isFunction(r) && isTotal(r) && x in dom(r)
    {
         var s := (set y | y in dom(r) && (x, y) in pairs(r) :: y);
         assert | s | > 0;
         var q :| q in s;
         return q;
    }
    */

    method relSToMapS<T>(r: relationS<T>) returns (m: map<T,T>)
        requires isFunctionS(r);
    {
        m := map[];
        var ps := pairsS(r);
        while (|ps| != 0)
            decreases ps
        {
            var p :| p in ps;
            m := m[ p.0 := p.1 ];
            ps := ps - { p };
        }
        return m;
    }


    method Main()
    {
        quiz3();

        var S := { 1, 2, 3 };
        var P := {(1,1), (2,2), (3,3), (3,2)};
        var R := relS(S, P);
        // var Q := relS(S, {(1,1), (2,5)}) // violates dom precondition

        var t := isTotalS(R);
        var s := isSurjectiveS(R);
        var p := isPartialS(R);
        var i := isInjectiveS(R);
        var f := isFunctionS(R);
        var b := isBijectiveS(R);
        var r := isReflexiveS(R);
        var y := isSymmetricS(R);
        var v := isTransitiveS(R);
        print "R ", isNt(t), " total\n";
        print "R ", isNt(s), " surjective\n";
        print "R ", isNt(p), " partial\n";
        print "R ", isNt(i), " injective\n";
        print "R ", isNt(f), " a function\n";
        print "R ", isNt(b), " bijective\n";
        print "R ", isNt(r), " reflexive\n";
        print "R ", isNt(y), " symmetric\n";
        print "R ", isNt(v), " transitive\n";
    }

    function method isNt(b: bool): string
    {
        if b then "is" else "isn't"
    }
}