include "functional.dfy"

module homework4
{
import opened functional
method sumto_verified(n: nat) returns (f: nat)
    ensures f == sumto(n)
    {
        var a: nat := 0;
        var i: nat := n;
        assert a + sumto(i) == sumto(n);
        while (i > 0) 
            invariant a + sumto(i) == sumto(n)
            decreases i;
        {
            a := a + i;
            i := i - 1;
        }
        return a;
    }

    method sum_squares_verified(n: nat) returns (f: nat)
        ensures f == sum_squares(n)
        {
            var a: nat := 0;
            var i: nat := n;
            assert a + sum_squares(i) == sum_squares(n);
            while (i > 0)
                invariant 0 <= i <= n;
                invariant a + sum_squares(i) == sum_squares(n);
                decreases i;
            {
                a := a + (i * i);
                i := i - 1;
            }
            return a;
        }

    method Main()
    {
        print "\n";
        var n: nat := 5;
        var r := sumto_verified(n);
        print "sumto ", n, " is ", r, "\n";
        r := sum_squares_verified(n);
        print "sum_squares ", n, " is ", r, "\n";
    }
}