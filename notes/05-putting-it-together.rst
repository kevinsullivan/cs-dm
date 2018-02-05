Integrating Formal Specification with Imperative Programming
============================================================

To get a clear sense of the potential differences in performance
between a pure functional program and an imperative program that
compute the same function, consider our recursive definition of the
Fibonacci function.

We start off knowing that if *n* is *0* or *1* the answer is *n*.  In
other words, the *sequence*, *fib(i)* of *Fibonacci numbers indexed by
i*, starts with, :math:`[0, 1, \ldots ]`. We start already having the
values of *fib(0)*, the first Fibonacci number and *fib(1)*, the
second. The third, *fib(2)* is then the sum of the previous two.  Note
that by convention we index sequences starating at zero rather than
one. The first element in such a sequence has index *0*, the second
has index *1*, and the *n'th* has index *n - 1*.

Now, for any index *i >= 1*, the next element, *fib(i+1)* is the sum
of the previous two elements, *fib(i-1)* and *fib(i)*. Let's call them
*fib0=fib(i-1), fib1=fib(i)*, and *fib2=fib(i+1)*. Given a *fib0* and
a *fib1* we compute *fib2* by adding *fib0* and *fib1*. 

Our recursive definition, *fib(n)* is pure math: elegant and precise.
And because we've written in a functional programming language, we can
even run it if we wish. An imperative program, by constrast, will just
repeated add the last two two known Fibonacci numbers together to get
the next one until the desired *nth* one is computed.

Now let's consider the evaluation of each program given the value, *n
= 7*. Start with the imperative program. The answers for the first two
values are zero and one. If *n* is either zero or one the answer is
just returned; otherwise it is computed and returned. In this case,
the program will repeatedly add together the last two known values of
the function (starting with the *0* and *1*) to obtain the next one.
It will then store (remember) the previous and current values of the
function to get ready for the next iteration of the loop, terminating
once the *n'th* value in the sequence of Fibonacci numbers has been
computed. The program returns that value.

Question: How many executions of the loop body are required to compute
*fib(5)*? Well, we need to execute it for values of *i* of *2, 3, 4,*
and *5*. It takes *4* **n-1* iterations. To compute the 10th element
requires that the loop body execute for *i* in the range (inclusive
of *[2, 3, ..., 10]*, which means nine iterations of the loop will be
required, or, again, *n-1*. Indeed, it's pretty easy to see that for
any value of *n*, *n-1* iterations of the loop body will be required
to compute the *nth* Fibonacci number.

The functional program, on the other hand, is evaluated by repeated
unfolding of nested recursive definitions until values are computed,
at which point the values are combined into a final result. Let's see
if we can see a pattern. We'll measure computational complexity now in
terms of the number of function evaluations (rather than loop bodies
executed).

To compute $fib(0)* or $fib(1)$ requires just $1$ function evaluation,
as these are base cases with no recursive calls to solve subproblems.
To compute *fib(2)* however requires *3* evalations of *fib*, one for
*2* and one for each of *1* and *0*. Those count as just one each as
there are no further recursive calls. So the relationship between *n*
and the number of function evaluations currently looks like this:
:math:`\{ (0,1), (1,1), (2,3), ... \}.`

What about when *n* is *3*?  Computing this requires answers for
*fib(2)*, costing *3* evaluations, and *fib(1)*, costing one, for a
total of *5* evaluations. Computing *fib(4)* requires answers for
*fib(3)* and *fib(2)*, costing *5 + 3*, or *8* evaluations, plus the
original evaluation is 9. For *fib(5)* we need *9* + *5*, or *14*,
plus the original makes $15* evaluations.  relation is like this:
:math:`\{ (0,1), (1,1), (2,3), (3,5), (4,9), (5, 15), ... \}.` So, in
general, the number of evaluations needed to evaluate *fib(i+1)* is
the sum of the numbers required to compute *fib(i)* and *fib(i-1) +
1.* Now that we see the formula, we can compute the next entry in the
sequence easily: the number of function evaluations needed to compute
*fib(6)* is *15 + 9 + 1*, i.e., 25. Computing the value of *fib(7)*
costs *41* evaluations; *fib(8), *67*l *fib(9), 109*, *fib(10), 177*
and *fib(11), 286* function evaluations.

With out imperative program, the number of loop body interations grows
linearly with *n*. We could say that the computational cost of running
the imperative program to compute *fib(n)*, let's call it *cost(n) is
just *n+1*. How does the cost of the (doubly) recursive program grow
as a function of *n*? Well, one thing to notice is that the cost of
computing the Fibonacci sequence is close to the Fibonacci sequence
itself! The first two values in the *cost* sequence are *1* and *1*,
and each subsequence element is the sum of the previous two *plus 1*.
It's not exactly the Fibonacci sequence, but it turns out to grow at
the same rate overall. Without getting into details, the Fibonacci
sequence, and thus also the cost of computing it recursively, grows at
an exponential rate, with an exponent of about *1.6*. Increasing *n*
by *1* does quite double the previous cost, but it does multiply it by
about *1.6*.

No matter how small the exponent, exponential functions eventually
grow very large very quickly. You can already see that the cost to
compute *fib(n)* recursively for values of *n* larger than just ten or
so is vastly greater than the cost to compute it iteratively. The math
(the recursive definition clear but inefficient. The program is
efficient, but woefully not transparent as to its function. We need
the latter program for practical computation. But how do we ensure
that hard to understand imperative code flawlessly implements the same
function that we expressed so elegantly in mathematical logic and its
computational expression in pure functional programming?

We address such problems by combining a few ideas. First, we use logic
to express *declarative* specifications that precisely define *what* a
given imperative program must do, an in particular what results it
must return as a function of the arguements it received.

We can use functions defined in the pure functional programming style
as specifications, e.g., as giving the mathematical definition of the
*factorial* function that an imperative program is meant to implement.

Second, we implement the specified program in an imperative language
in a way that supports logical reasoning about its behavior. What kind
of support is needed to facilitate logical reasoning is broached in
this chapter. For example, we have to specify not only the desired
relationship between argument and result values, but also how loops
are designed to work in our code; and we need to design loops in ways
that make it easier to explain in formal logic how they do what they
are meant to do. 

Finally, we use logical proofs to *verify* that the program satisifies
its specification.

We develop these idea in this chapter. First we explain how formal
specifications in mathematical logic for imperative programs are often
organized. Next we explore how writing imperative programs without the
benefits of specification languages and verifications tools can make
it hard to spot bugs in code. Next we enhance our implementation of
the factorial function with specifications, show how Dafny flags the
bug, and fix out program. Doing this requires that we deepen the way
we understand loops. We end with a detailed presentation of the design
and verification of an imperative program to compute elements in the
Fibonacci sequence. Given any natural number *n*, our program must
return the value of *fib(n)*, but it must also do it efficiently.  The
careful design of a loop is once again the very heart of the problem.
We will see how Dafny can help us to reason rigorously about loops,
and that, with just a bit of help, it can reason about them for us.



Logical Specification
---------------------

First, we use mathematical logic to *declaratively specify* properties
of the behaviors that we require of programs written in *imperative*
languages. For example, we might require that, when given any natural
number, $n$, a program compute and return the value of the $factorial$
of $n$, the mathematical definition of which we've given as $fact(n)$.

Specifications about required relationships between argument values
and return results are especially important. They specify *what* a
program must compute without specifying how. Specifications are thus
*abstract*: they omit *implementation details*, leaving it to the
programmer to decide how best to *refine* the specification into a
working program.

For example we might specify that a program (1) must accept any
integer valued argument greater than or equal to zero (a piece of a
specification that we call a *precondition*), and (2) that as long as
the precondition holds, then it must return the factorial of the given
argument value (a *postcondition*).

In purely mathematical terms, a specification of this kind defines a
*binary relation* between argument and return values, and imposes on
the program a requirement that whenever it is given the first value in
such a pair, it must compute a second value so that the :math:`(first
value, second value)` pair is in the specified relation.

A binary relation in ordinary mathematics is just a set of pairs of
values. A function is a special binary relation with at most one pair
with a given first value. A function is said to be a *single-valued*
relation.

For example, pairs of non-negative integers in the relation that
constitutes the factorial function include :math:`(0,1), (1,1), (2,2),
(3,6), (4,24)` and :math:`(5,120)`, but not :math:`(5,25)`.

On the other hand, square root is a relation but not a *function*. It
is not singled valued. Both :math:`(4,2)` and :math:`(4,-2)`, two
pairs with the same first element but different second elements, are
in the relation. That is because both *2* and *-2* are squarer roots
of *4*.  The *positive square root* relation, on the other hand, is a
function, comprising those pairs in the square root relation where
both elements are non-negative. It thus includes :math:`(4,2)` but
not  :math:`(4,-2)`.

We could formulate the square root *relation* as a *function* in a
different way: by viewing it as a relation that associates with each
non-negative integer the single *set* of its square roots. The pair
:math:`(4, \{2, -2\}` is in this relation, for example. The relation is
now also a function in that there is only one such pair with a given
first element.

Now what we mean when we say that a program computes a function or a
relation is that whenever it is given a valid argument representing
the *first* value of a pair in the relation, it computes a *second*
value such that the pair, :math:`(first, second)` is in the given
relation. When we say, for example, that a program *computes the
factorial function*, we mean that if we give it a non-negative number,
*n*, it returns a number *m* such that the pair *(n,m)* is *in* the
relation. And for *(n,m)* to be in the relation it must be that
:math:`m = fact(n)`. The program thus has to return :math:`fact(n)`.

A program that computes a *function* is deterministic, in the sense
that it can return at most one result: because there is at most one
result. When a program computes a relation that is not a function, it
can return any value, *m*, where *(n,m)* is in the specified relation.

Rigorous Implementation
-----------------------

Having written a formal specification of the required *input-output*
behavior of a program, we next write imperative code in a manner, and
in a language, that supports the use of formal logic to *reason* about
whether the program refines (implements) its formal specification. One
can use formal specifications when programming in any language, but it
helps greatly if the language has strong, static type checking. It is
even better if the language supports formal specification and logical
reasoning mechanisms right alongside of its imperative and functional
programming capabilities. Dafny is such a language.

In addition to choosing a language with features that help to support
formal reasoning (such as strong, static typing), we sometimes also
aim to write imperative code in a way that makes it easier to reason
about formally (using mathematical logic). As we will see below, for
example, the way that we write our while loops can make it easier or
harder to reason about their correctness.


Formal Verification
-------------------

Our ultimate aim to deduce that, as written, a program satisfies its
input-output specification.  In more detail, if we're given a program,
*C* with a precondition, *P*, and a postcondition *Q*, we want a proof
that verifies that if *C* is started in a state that satisfies *P* and
if it terminates (doesn't go into an infinite loop), that it ends in a
state that satisfies *Q*. We call this property *partial correctness*.

We write the proposition that *C* is partially correct in this sense
(that if it's started in a state that satisfies the assertion, *P*,
and if it terminates then, it will do so in a state that satisfies
*Q*) as :math:`P {C} Q.` This is a so-called *Hoare triple* (named
after the famous computer scientist, Sir Anthony (Tony) Hoare. It is
nothing other than a proposition that claims that *C* satisfies its
specification.

In addition to a proof of partial correctness, we usually do want to
know that a program also does always terminate. When we have a proof
of both :math:`P \{C\} Q` and that the program always terminates, then
we have a proof of *total correctness*. Dafny is a programming system
that allows us to specify *P* amd *Q* and that then formally, and to a
considerable extent automatically, verifies `P \{C\} Q` and termination.
That is, Dafny produces proofs of total correctness.

It is important to bear in mind that a proof that a program refines
its formal specification does not necessarily mean that it is fit for
its intended purpose! If the specification is wrong, then all bets are
off, even if the program is correct relative to its specification.
The problem of *validating* specification againts real-world needs is
separate from that of *verifying* that a given program implements its
specification correctly.

Case Study: Implementing the Factorial Function
-----------------------------------------------

So far the material in this chapter has been pretty abstract. Now
we'll see what it means in practice. To start, let's consider an
ordinary imperative program, as you might have written in Python or
Java, for computing the factorial function. The name of the function
is the only indication of the intended behavior of this program. There
is no documented specification. The program takes an argument of type
nat (which guarantees that the argument has the property of being
non-negative). It then returns a nat which the programmer implicitly
claims (given the function name) is the factorial of the argument.

.. code-block:: dafny

   method factorial(n: nat) returns (f: nat) 
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
       f := a;
   }

Sadly, this program contains a bug. Try to find it. Reason about the
behavior of the program when the argument is 0, 1, 2, 3, etc.  Does it
always compute the right result? Where is the bug? What is wrong? And
how could this logical error have been detected automatically?

The problem is that the program lacks a complete specification. The
program does *something*, taking a nat and possibly returning a nat
(unless it goes into an infinite loop) but there's no way to analyze
its correctness in the absence of a specification that defines what
*right* even means.

Now let's see what happens when we make the specification complete.
The precondition will continue to be expressed by the type of the
argument, *n*, being *nat*. However, we have added a postcondition
that requires the return result to be the factorial of *n*. Note that
we used our functional definition of the *factorial* function in the
*specification* of our imperative code. The pure functional program is
really just a mathematical definition of factorial. What we assert
with the postcondition is thus that the imperative program computes
the factorial function as it is defined in pure mathematics.

.. code-block:: dafny

   method factorial(n: nat) returns (f: nat) 
       ensures f == fact(n)
   {
       if (n == 0) 
       { 
           return 1;
       }
       var t := n;
       var a := 1;
       while (t !=  0)
       {
           a := a * n;
           t := t - 1;
       }
       return a;
   }

Dafny now reports that it cannot guarantee---formally prove to
itself---that the *postcondition* is guaranteed to hold. Generating
proofs is hard, not only for people but also for machines. In fact,
one of seminal results of 20th century mathematical logic was to prove
that there is no general-purpose algorithm for proving propositions in
mathematical logic. That's good news for mathematicians!  If this
weren't true, we wouldn't need them!

So, the best that a machine can do is to try to find a proof for any
given proposition. Sometimes proofs are easy to generate. For example,
it's easy to prove *1 = 1* by the *reflexive* propery of equality.
Other propositions can be hard to prove. Proving that programs in
imperative languages satisfy declarative specifications can be hard.


When Dafny fails to verify a program (find a proof that it satisfies
its specification), there is one of two reasons. Either the program
really does fail to satisfy its specificaiton; or the program is good
but Dafny does not have enough information to know how to prove it. 

With the preceding program, the postcondition really isn't satisfied
due to the bug in the program. But even if the program were correct,
Dafny would need a little more information than is given in this code
to prove it. In particular, Dafny would need a litte more information
about how the while loop behaves. It turns out that providing extra
information about while loops is where much of the difficulty lies.

A Formally Verified Implementation of the Factorial Function
------------------------------------------------------------

.. code-block:: dafny

Here's verified imperative program for computing factorial. We start
by documenting the overall program specification.

.. code-block:: dafny

    method verified_factorial(n: nat) returns (f: nat) 
        ensures f == fact(n)



Now for the body of the method. First, if we're looking at the case
where *n==0* we just return the right answer immediately. There is
no need for any further computation.
	
.. code-block:: dafny

        if (n == 0) 
        { 
            return 1;
        }



The rest of the code handles the case where *n > 1*. At this point in
the program execution, we believe that *n* must be greater than zero,
as we would have just returned if it were zero, and it can't be
negative because its type is *nat*. We can nevertheless formally
assert (write a proposition about the state of the program) that *n*
is greater than zero. Dafny will try to (and here will successfully)
verify that the assertion is always true at this point in the program.

.. code-block:: dafny

        assert n > 0;

Strategy: use a while loop to compute the answer. We can do this by
using a variable, a, to hold a "partial factorial value" in the form
of a product of the numbers from n down to a loop index, "i," that we
start at n and decrement down, terminating the loop when *n==0*. At
each point just before, during, and right after the loop, *a* is a
product of the numbers from *n* down to *i*, and the value of *i*
represents how much of this product-computing work remains to be
done. So, for example, if we're computing factorial(10) and a holds
the value *10 \* 9*, then *i* must be *8* because the task of
multiplying *a* by the factors from *8* down to *1* remains to be
done. A critical "invariant" then is that if you multiply *a* by the
factorial of *i* you get the final answer, the factorial of *n*.
And in particular, when *i* gets down to *0*, *a* must contain the
final result, because *a \* fact(0)* will then equal *fact(n)* and
*fact(0)* is just *1*, so *a* must equal *fact(n)*. This is how we
design loops so that we can be confident that they do what we want
tem to do.

Step 1. Set up state for the loop to work. We first initializie a := 1
and i := n and check that the invariant holds. Note that we are using
our pure functional math-like definition of fact as a *specification*
of the factorial function we're implementing.  

.. code-block:: dafny

        var i: nat := n;    // nat type of i explicit
        var a := 1;         // can let Dafny infer it

In Dafny, we can use matnematical logic to express what must be true
at any given point in the execution of a program in the form of an
"assertion." Here we assert that our loop invariant holds. The Dafny
verifier tries to prove that the assertion is a true propsition about
the state of the program when control reaches this point in the
execution of this program.

.. code-block:: dafny

        assert a * fact(i) == fact(n); // "invariant"


Step 2: Now evaluate the loop to get the answer. To evaluate a loop,
first, evaluate the loop condition (i > 0).Then , if the result is
false, terminate the loop. Otherwise, evaluate the loop body, then
iterate (run the loop again, starting by evaluating the loop
condition).  

Note that we can deduce that the loop body is going to execute at
least once. It will run if i > 0. What is i? We initialized it to n
and haven't change it since then so it must still be equal to n. Do we
know that n is greater than 0? We do, because (1) it can't be negative
owning to its type, and (2) it can't be 0 because if it were 0 the
program would already have returned. But we can now do better than
just reasoning in our heads; we can use logic to express what we
believe to be true and let Dafny try to check it for us automatically.


.. code-block:: dafny

	assert i > 0;
        
Let's just think briefly about cases. We know i can't be zero. It
could be one. If it's one, then the loop body will run. The loop body
will run. a, which starts at 1, will be multiplied by i, which is 1,
then i will be decremented.  It will have the value 0 and the loop
will not run again, leaving a with the value 1, which is the right
answer. So, okay, let's run the loop.  
        

.. code-block:: dafny

        while (i >  0)
            invariant 0 <= i <= n
            invariant fact(n) == a * fact(i) 
        {
            a := a * i;
            i := i - 1;
        }

At this point, we know that the loop condition is false. In English,
we'd say it is no longer true that i is greater than zero." We can do
better that saying this in natural language then forgetting it. We can
use formal logic to formalize and document our belief and if we do
this then Dafny pays us well for our effort by checking that our
assertion is true.  
 
.. code-block:: dafny

       assert !(i > 0);

We can also have Dafny check that our loop invariant still holds.


.. code-block:: dafny

        assert a * fact(i) == fact(n);

And now comes the most crucial step of all in our reasoning. We can
deduce that a now holds the correct answer. That this is so follows
from the conjunction of the two assertions we just made. First, that i
is not greater than 0 and given that its type is nat, the only
possible value it can have now is 0. And that's what we'd expect,
because that's the condition on which the loop terminates, which is
just did! But better than just saying it, let us also formalize,
document, and check it.

.. code-block:: dafny

        assert i == 0;

Now it's easy to see. No matter what value i has, a * fact(i) ==
fact(n), and i == 0, so we have a * fact(0) == fact(n), and we know
that fact(0) is 1 because we see that in the very mathematical
definition of fact, so it must be that a = fact(n). Dafny can check!
        

.. code-block:: dafny

        assert a == fact(n);

We thus have the answer we need to return.  Dafny verifies that our
program satisfies its formal specification. We no longer have to
pray. We *know* that our program is right and Dafny confirms our
belief. 


.. code-block:: dafny

	return a;

Mathematical logic is to software as the calculus is to physics and
engineering.  It's not just an academic curiosity. It is a critical
intellectual tool, inceasingly used for precise specification and
semi-automated reasoning about and verification of real programs. 

Case Study: Verified Implementation of the Fibonacci Function
-------------------------------------------------------------

Similarly, here an imperative implementation of the fibonacci
function, without a spec.

.. code-block:: dafny

    method fibonacci(n: nat) returns (r: nat)
        ensures r == fib(n)
    

Now for the body. First we represent values for the two
cases where the result requires no further computation.
Initially, *fib0* will store the value of *fib(0)* and
*fib1* will store the value of *fib(1)*.

.. code-block:: dafny

        var fib0, fib1 := 0, 1; //parallel assmt

Next, we test to see if either of these cases applies,
and if so we just return the appropriate result. 

.. code-block:: dafny


        if (n == 0) { return fib0; }
        if (n == 1) { return fib1; }


At this point, we know something more about the state of the program
than was the case when we started. We can deduce, which is to say that
we know, that *n* has to be greater than or equal to *2*. This is
because it initially had to be greater than or equal to zero due to
its type, and then we would already have returned if it were *0* or
*1*, to it must now be *2* or greater. We can document the belief
that the current state of the program has to property that the value
of the variable *n* is greater than or equal to *2*, and Dafny will
verify this assertion for us.

.. code-block:: dafny

        assert n >= 2;

So now we have to deal with the case where *n >= 2*. Our strategy for
computing fib(n) in this case is to use a while loop with an index i.
Our design will be based on the idea that at the beginning and end of
each loop iteration (we are currently at the beginning), we will have
computed fib(i) and that its value is stored in fib1. We've already
assigned the value of fib(0) to fib0, and of fib(1) to fib1, so to set
up the desired state of affairs, we should initialize *i* to be *1*.

.. code-block:: dafny

        var i := 1;


We can state and Dafny can verify a number of conditions that we
expect and require to hold at this point. First, *fib1* equals
*fib(i)*. Now to compute the next (*i+1*) Fibonacci number, we need
not only the value of $fib(i)* but also *fib(i-1)*. We will thus also
want *fib0* to hold this value at the start and end of each loop
iteration, and indeed we do have that state of affairs right now.

.. code-block:: dafny

        assert fib1 == fib(i);
        assert fib0 == fib(i-1);

To compute *fib(n)* for any *n* greater than or equal to *2* will
require at least one execution of the loop body. We'll thus set our
loop condition to be $i < n$. This ensures that the loop body will
run, as *i* is *1* and *n* is at least *2*, so the condition *i < n*
is *true*, which dictates that the loop body must be evaluated.

Within the loop body we'll compute fib(i+1) (we call it *fib2* within
the loop) by adding together *fib0* and *fib1*; then we increment i;
then we update *fib0* and *fib1* so that for the *new* value of *i*
they hold *fib(i-1)* and *fib(i)*. To do this we assign the initial
value of *fib1* to *fib0* and the value of *fib2* to *fib1*. 

Let's work an example. Suppose *n* happens to be *2*. The loop body
will run, and after the one execution, *i* will have the value, *2*;
*fib1* will have the value of $fib(2)$, and *fib0* will have the value
of *fib(1)$. Because *i* is now *2* and *n* is still *2*, the loop
condition will now be false and the loop will terminate. The value of
*fib1* will of course be *fib(i)* but now we'll also have that *i ==
n* (it takes a little reasoning to prove this), so *fib(i)* will be
*fib(n)*, which is the result we want and that we return.

We can also informally prove to ourself that this strategy gives us
a program that always terminates and returns a value. That is, it does
not go into an infinite loop. To see this, note that the value of *i*
is initally less than or equal to *n*, and it increases by only *1* on
each time through the loop. The value of *n* is finite, so the value
of *i* will eventually equal the value of *n* at which point the loop
condition will be falsified and the looping will end.

That's our strategy. So let's go. Here's the while loop that we have
designed. And here, for the first time, we see something crucial. We
tell Dafny about certain properties of the state of the program that
hold both before and after every execution of the loop body. We call
such properties *invariants*. Dafny needs to know these invariants to
prove to itself (and to us) that the loop does what it is intended to
do: that the result at the end will be as desired.

.. code-block:: dafny

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


The invariants are just the conditions that we required to hold for
our design of the loop to work. First, *i* must never exceed *n*. If
it did, the loop would spin off into infinity. Second, to compute the
next (the *i+1st)* Fibonacci number we have to have the previous *two*
in memory. So *fib0* better hold *fib(i-1)* and *fib1*, *fib(i)*. Note
that these conditions do not have to hold *within* the execution of
the loop body, but they do have to hold before before and after each
execution.

The body of the loop is just as we described it above, and we can use
our own minds to deduce that if the invariants hold before the loop
body runs (and they do), then they will also hold after it runs. We
can also see that after the loop terminates, it must be that *i==n*.
This is because we know that it's always true that *i <= n* and the
loop condition must now be false, which is to say that *i* can no
longer be strictly less than *n*, so *i* must now equal *n*. Logic
says so, and logic is right. What is amazing is that we can write
these assertions in Dafny if we wish to, and Dafny will verify that
they are true statements about the state of the program after the
loop has run. We have *proved* (or rather Dafny has proved and we
have recapitulated the proof in this sequence of assertions) that
we have without a doubt computed the right answer. Dafny has also
proved to itself that the loop always terminates, and so we have
in effect a formal proof of total correctness for this program.

.. code-block:: dafny

        assert i <= n;      // invariant
        assert !(i < n);    // loop condition is false
        assert (i <= n) && !(i < n) ==> (i == n);
        assert i == n;      // deductive conclusion
        assert fib1 == fib(i); // invariant
        assert fib1 == fib(i) && (i==n) ==> fib1 == fib(n);
        assert fib1 == fib(n);
        return fib1;


What is Dafny?
--------------

Dafny is a cutting-edge software language and tooset developed at
Microsoft Research---one of the top computer science research labs in
the world---that provides such a capability. We will explore Dafny and
the ideas underlying it in the first part of this course, both to give
a sense of the current state of the art in program verification and,
most importantly, to explain why it's vital for a computer scientist
today to have a substantial understanding of logic and proofs along
with the ability to *code*.

Tools such as TLA+, Dafny, and others of this variety give us a way
both to express formal specifications and imperative code in a unified
way (albeit in different sub-languages), and to have some automated
checking done in an *attempt* to verify that code satisfies its spec.

We say *attempt* here, because in general verifying the consistency of
code and a specification is a literally unsolvable problem. In cases
that arise in practice, much can often be done. It's not always easy,
but if one requires ultra-high assurance of the consistency of code
and specification, then there is no choice but to employ the kinds of
*formal methods* introduced here.


To understand how to use such state-of-the-art software development
tools and methods, one must understand not only the language of code,
but also the languages of mathematical logic, including set and type
theory. One must also understand precisely what it means to *prove*
that a program satisfies its specification; for generating proofs is
exactly what tools like Dafny do *under the hood*.

A well educated computer scientist and a professionally trained
software developer must understand logic and proofs as well as coding,
and how they work together to help build *trustworthy* systems. Herein
lies the deep relevance of logic and proofs, which might otherwise
seem like little more than abstract nonsense and a distraction from
the task of learning how to program.

