include "functional.dfy"

module imperative
{
    /* 
       Allow use of definitions in functional
       module without prefixes.
    */
    import opened functional

    /*
    Here's a typical imperative program for 
    computing the factorial function. It 
    documents the specification it implements
    in a comment akin to the "doc strings" that
    one uses in Python programs to document the
    specifications that procedures implement.
    The problem with this code is that there
    are no check that it actually does what
    it says it does. In fact, it contains an
    error. Read the program to see if you can
    find the error before you look at the next
    program in this file, in which the error is
    corrected. You can see that there's a major
    erroy by just test-running this program and
    checking the output. It's clearly wrong.
    */
    method factorial(n: nat) returns (f: nat) 
    // For any n, return the factorial of n
    {
        if (n == 0) 
        { 
            return 1;
        }
        var t: nat := n;
        var a: nat := 1;
        while (t !=  0)
        {
            a := a * n;
            t := t - 1;
        }
        return a;
    }

    /*
    Can the incorporation of machine-checkable
    logical specifications in code help us to
    avoid such errors? The answer is yes. Let's
    see how.

    /*
    Here's an imperative program for computing factorial.
    */
    method verified_factorial(n: nat) returns (f: nat) 
        ensures f == fact(n)
    {
        if (n == 0) 
        { 
            return 1;
        }
        var t: nat := n;
        var a: nat := 1;
        while (t !=  0)
            invariant 0 <= t <= n
            invariant fact(n) == a * fact(t) 
        {
            a := a * t;
            t := t - 1;
        }
        // here we know fact(n) == a * fact(t) AND t == 0
        // from these two facts we can conclude that a == what?
        return a;
    }


    /*
    Similarly, here an imperative implementation 
    of the fibonacci function, without a spec.
    */
    method fibonacci(n: nat) returns (r: nat)
    {
        if (n < 2) return n;
        var fib_minus_2 := 0;
        var fib_minus_1 := 1;
        var fib_current := 0;
        var ind := 2;
        while (ind <= n) 
        {
            fib_current := fib_minus_2 + fib_minus_1;
            fib_minus_2 := fib_minus_1;
            fib_minus_1 := fib_current;
            ind := ind + 1;
        }
        return fib_current;
    }


    method verified-fibonacci(n: nat) returns (r: nat)
        ensures r == fib(n)
    /* a verified implementation goes here! */

}




