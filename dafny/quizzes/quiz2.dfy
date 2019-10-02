include "functional.dfy"

module quiz2
{
    import opened functional
    method sum_to_impl(n: nat) returns (r: nat)
        ensures r == sumto(n)
    {
        if (n == 0) { return 0; }   // unnecessary code!
        var acc: nat := 0;
        var i: nat := n;
        assert acc + sumto(i) == sumto(n);
        while (i > 0)
            invariant acc + sumto(i) == sumto(n);
        {
            acc := acc + i;
            i := i - 1;
        }
        return acc;
    }

    method Main()
    {
        var n := sum_to_impl(5);
        print n;
    }
}