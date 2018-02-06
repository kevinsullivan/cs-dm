include "functional.dfy"

module imperative_fibonacci
{
    /* 
       Allow use of definitions in functional
       module without prefixes.
    */
    import opened functional

    /*
    Here's an imperative implementation of the Fibonacci
    function without a specification or any verification.
    Unforunately, this program contains a bug relative to
    what we understand intuitively to be the intent of this
    code. Without a documented spec, though, there is just
    no way for a programming system to detect such an error.
    */
    method fibonacci_unverified(n: nat) returns (f: nat)
    {
        // For index 0 or 1 just return result directly
        if (n < 2) { return n; }

        /*
        Otherwise compute result by iterating. Start
        by initializing state for loop, with fib0 and
        fib1 containing the last two known values of
        the sequence and i being the index of the last
        computed value.
        */
        var fib0 := 0;
        var fib1 := 1;
        var i := 1;

        /*
        Given that we maintain the "invariant" that i 
        is always the index of the last computed value
        and that we want to compute fib(n), we want our
        loop to stop when i==n. To accomplish this, we
        use a loop condition (i < n), and given that 
        we are starting with i definitely less than n
        (as i is 1 and n is at least 2, otherwise we
        would have returned already), we know that the
        loop will eventually hit a state where i==n, and
        at that point it will stop.
        */
        while (i < n)
        {
            /*
            Within each iteration of the loop (right 
            here) we compute the next value in the 
            Fibonacci sequence (as fib0+fib1), then 
            we update fib0 to be the current (fib1)
            and next (fib0+fib1) values for the next 
            iteration possible iteration of the loop.
            */
            fib0, fib1 := fib0, fib0+fib1;
            /* 
            And we increment i, re-establishing the
            invariant that outside of the loop body,
            i is always the index of the last computed
            value of the function.
            */
            i := i + 1;
        }
        /*
        At this point we know that i is the index of
        the last computed Fibonacci value, that fib1
        is fib(i), that i == n, and therefore that 
        fib1 is fib(n), which is the result we want
        to return!
        */
        return fib1;
    }

    /*
    Similarly, here an imperative implementation 
    of the fibonacci function, verified against 
    a formal spec.
    */
    method fibonacci_verified(n: nat) returns (r: nat)
        ensures r == fib(n)
    {
        /*
            Represent values for two base cases.
        */
        var fib0, fib1 := 0, 1; //parallel assmt

        /*
           Return base case result if appropriate
        */
        if (n == 0) { return fib0; }
        if (n == 1) { return fib1; }

        /*
           At this point, we know n (a nat) >= 2.
        */
        assert n >= 2;

        /*
           Our strategy for computing fib(n) is
           to use a while loop with an index i.
           Our design will be based on the idea
           that at the beginning and end of each 
           loop iteration, that we have computed
           fib(i) and that its value is stored in
           fib1. Then within the loop body we'll 
           compute fib(i+1) and then increment i.
 
           At this point, we've already computed
           fib(0), stored in fib0, and and fib(1), 
           in fib1, so we should initialize i to 
           be 1. 
           
           We'll want to terminate the loop when 
           i == n, at which point fib1 should
           have the value fib(i), where i ==n,
           so fib(i) will be fib(n). That is the
           strategy. So let's go.
        */
        var i := 1;

        /*
            We can state and Dafny can verify a
            number of conditions that we expect
            and require to hold at this point.
        */
        assert fib1 == fib(i);
        assert fib0 == fib(i-1);
        assert i <= n;


        /*
            Here's the loop. We can be sure it will
            run at least once, because at this point
            n must be greater than or equal to 2 ...
        */
        assert n >= 2;
        /*
            and we know that i is 1, and 1 < 2, which
            satisfies the loop condition. If n were to
            be equal to 2, the loop body would run, the
            value of fib2 would be set to the sum of 
            the current values of fib1 and fib0, giving
            us fib2; then fib0 will be set to the current
            value of fib1, fib1 will be set of the value
            of fib2, and i will be incremented, at which
            point the critical condition will be restored: 
            fib1 == fib(i), but where i is now equal to 2.
            We also know that i started off less than n,
            it gets incremented by only 1 each time the
            loop body executes, and the loop terminates
            when it is no longer true that i < n. So it
            remains true at all times that i <= n. For
            Dafny to be able to verify that a loop does
            what it's meant to do, we have to declare 
            the invariants that are required to hold.
        */
        while (i < n) 
            invariant i <= n;
            invariant fib0 == fib(i-1);
            invariant fib1 == fib(i);
        {
            var fib2 := fib0 + fib1;
            fib0 := fib1;
            fib1 := fib2;
            i := i + 1;
        }
        /*
            So we know that every iteration of the loop
            body has preserved the condition that fib1 is
            equal to fib(i). What else do we know? Well,
            a little bit of logical reasoning leads us to
            conclude that i == n. Combining these facts
            then leads to the final result: fib1==fib(n)
        */
        assert i <= n;      // invariant
        assert !(i < n);    // loop condition is false
        assert (i <= n) && !(i < n) ==> (i == n);
        assert i == n;      // deductive conclusion
        assert fib1 == fib(i); // invariant
        assert fib1 == fib(i) && (i==n) ==> fib1 == fib(n);
        assert fib1 == fib(n);

        /*
            We now have a proven-correct result!
        */
        return fib1;
    }
}