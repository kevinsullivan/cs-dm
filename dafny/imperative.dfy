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
    Here's an imperative program for computing factorial.
    */
    method verified_factorial(n: nat) returns (f: nat) 
        ensures f == fact(n)
    {
        // If base case, return result without recursion
        if (n == 0) 
        { 
            return 1;
        }

        // The rest of the code handles recursive case
        assert n > 0;

        /*
           Strategy: use a while loop to compute the
           answer. We can do this by using a variable,
           a, to hold a "partial factorial value" in
           the form of a product of the numbers from 
           n down to a loop index, "i," that we start
           at n and decrement down, terminating the
           loop when n==0. At each point just before,
           during, and right after the loop, a is a
           product of the numbers from n down to i, 
           and the value of i represents how much of
           this product-computing work remains to be
           done. So, for example, if we're computing
           factorial(10) and a holds the value 10 * 9,
           then i must be 8 because multiplying a by
           the factors from 8 down to 1 remains to be
           done. A critical "invariant" then is that
           if you multiply a by the factorial of i 
           you get the final answer, which is to say
           the factorial of n.  
        */

        /* 
           Step 1. Set up state for the loop to work.

           We first initializie a := 1 and i := n and
           check that the invariant holds. Note that
           we are using our pure functional math-like
           definition of fact as a *specification* of
           the factorial function we're implementing.
        */
        var i: nat := n;    // nat type of i explicit
        var a := 1;         // can let Dafny infer it

        /*
           In Dafny, we can use matnematical logic to
           express what must be true at any given point
           in the execution of a program in the form of
           an "assertion." Here we assert that our loop
           invariant holds. The Dafny verifier tries to
           prove that the assertion is a true propsition
           about the state of the program when control
           reaches this point in the execution of this
           program.
        */
        assert a * fact(i) == fact(n); // "invariant"


        /*
            Step 2: Now evaluate the loop to get the
            answer.

           To evaluate a loop, first, evaluate the 
           loop condition (i > 0).Then , if the result 
           is false, terminate the loop. Otherwise, 
           evaluate the loop body, then iterate (run 
           the loop again, starting by evaluating the
           loop condition).     
        */

        /*
           Note that we can deduce that the loop body
           is going to execute at least once. It will 
           run if i > 0. What is i? We initialized it
           to n and haven't change it since then so it
           must still be equal to n. Do we know that 
           n is greater than 0? We do, because (1) it
           can't be negative owning to its type, and 
           (2) it can't be 0 because if it were 0 the
           program would already have returned. But we
           can now do better than just reasoning in our
           heads; we can use logic to express what we
           believe to be true and let Dafny try to 
           check it for us automatically.
        */
        assert i > 0;
        
        /*
        Let's just think briefly about cases. We know
        i can't be zero. It could be one. If it's one,
        then the loop body will run. The loop body will
        run. a, which starts at 1, will be multiplied 
        by i, which is 1, then i will be decremented.
        It will have the value 0 and the loop will not
        run again, leaving a with the value 1, which 
        is the right answer. So, okay, let's run the
        loop.
        */
        
        while (i >  0)
            invariant 0 <= i <= n
            invariant fact(n) == a * fact(i) 
        {
            a := a * i;
            i := i - 1;
        }

        /*
           At this point, we know that the loop 
           condition is false. In English, we'd
           say it is no longer true that i is greater
           than zero." We can do better that saying
           this in natural language then forgetting
           it. We can use formal logic to formalize 
           and document our belief and if we do this
           then Dafny pays us well for our effort 
           by checking that our assertion is true. 
        */
        assert !(i > 0);

        /*
            We can also have Dafny check that our
            loop invariant still holds. 
        */
        assert a * fact(i) == fact(n);

        /*
            And now comes the most crucial step of 
            all in our reasoning. We can deduce that
            a now holds the correct answer. That this
            is so follows from the conjunction of the
            two assertions we just made. First, that
            i is not greater than 0 and given that its
            type is nat, the only possible value it
            can have now is 0. And that's what we'd
            expect, because that's the condition on
            which the loop terminates, which is just
            did! But better than just saying it, let
            us also formalize, document, and check it.
        */
        assert i == 0;

        /*
           Now it's easy to see. No matter what value
           i has, a * fact(i) == fact(n), and i == 0, so
           we have a * fact(0) == fact(n), and we know
           that fact(0) is 1 because we see that in the
           very mathematical definition of fact, so it
           must be that a = fact(n). Dafny can check!
         */
        assert a == fact(n);

        /*
            We thus have the answer we need to return.
            Dafny verifies that our program satisfies
            its formal specification. We no longer have
            to pray. We *know* that our program is right
            and Dafny confirms our belief.
        */
        return a;

        /*
            Mathematical logic is to software as the 
            calculus is to physics and engineering.
            It's not just an academic curiosity. It is
            a critical intellectual tool, inceasingly
            being used for precise for specification 
            and verification of practical programs.
        */
    }

    /*
    Similarly, here an imperative implementation 
    of the fibonacci function, without a spec.
    */
    method fibonacci(n: nat) returns (r: nat)
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