function sumSquares(n: nat): nat
    {
        if (n==0) then 0 else n * n + sumSquares(n-1)
    }

   
    method sumSquares_impl(n: nat) returns (r: nat)
        ensures r == sumSquares(n)
    {
        if (n == 0) { return 0;}

        assert n > 0;

        var i := n;
        var a := 0;

        assert sumSquares(i) + a == sumSquares(n);

        while (i > 0)
            invariant sumSquares(i) + a == sumSquares(n);
        {
            a := a + i * i;
            i := i - 1;
        }
        assert i == 0;          // loop condition is false
        assert sumSquares(i) + a == sumSquares(n); // invariant holds

        // step-by-step argument from these facts that a is the answer
        assert (i == 0) && sumSquares(i) + a == sumSquares(n) ==>  
                                                    a == sumSquares(n);
        assert a == sumSquares(n);

        // we've got our answer; return it
        return a;
    }


    method pathFun() 
    {
        assert 1 == 1;
        var x := 2;

        var i := 5;
        while (i > 0)
        {
            x := 3;
            if ( i == 1) { x := 2; }
            i := i - 1;
        }
        assert x == 2;
    }
  