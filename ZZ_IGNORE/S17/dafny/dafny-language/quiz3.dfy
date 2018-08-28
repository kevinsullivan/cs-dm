module quiz3
{
    method quiz3()
    {
        // set comprehension (set builder) notation
        // all the even integers in [0..100] inclusive
        var S1 := set s | 0 <= s <= 50 :: 2 * s;
        print S1, "\n";

        // The subset of numbers in S1 that are < 25
        var T1 := set t | t in S1 && t < 25;
        print T1, "\n";

        // The set of ordered pairs in the set product S1 X T1
        var Q := set s, t | s in S1 && t in T1 :: (s, t);
        print Q, "\n";

        // Set cardinality
        print | Q |, "\n";

        // Set difference
        var S2 := S1 - T1;
        print S2, "\n";

        // Powerset!
        var S := { 1, 2, 3 };
        var P := set R | R <= S;
        print P;
    }


    // A polymorphic set product "operator" in one line of code
    function method set_product<T1,T2>(s1: set<T1>, s2: set<T2>): set<(T1,T2)>
    {
        set q, r | q in s1 && r in s2 :: (q,r)
    }
}