/*
An "identity function" for values of type nat.
Returns whatever value you pass to it. Note
that the body of a pure function is not usual
sequential code but simply an expression that
computes the desired return value. 
*/
function method id_int (x: int): int { x }

/*
The "function method" declaration indicates two
things. First, the code will be written in a pure
functional style. Second, the code can be called
from imperative code. Dafny compiles "function 
methods" into executable code. Code declared to
be just a "function" in Dafny can be used in pre-
and post-conditions and in other specifications,
and so can be involved in verification, but such
functions are not compiled to executable code.
*/


// Return sequare of given int as an int
function method square (x: int): int { x * x }


// Return the successor of int x as an int
function method inc (x: int): int { x + 1 }


// Given int x computes square of its successor
function method h (x: int): int { square(inc(x)) }


// Computes factorial of any non-negative integer
function method fact(n: int): int 
    requires n >= 0 // for recursion to be well founded
{ 
    if (n==0) 
    then 1 
    else n * fact(n-1) 
}
/*
The fact function computes the factorial of any non-negative 
integer. Recall from mathematics that the factorial of 0 is 1, 
and the factorial of n, for any n>0, is n*factorial(n-1). The 
factorial of 5 is thus 5 * factorial(4), and this of course is 
5 * (4 * factorial(3)). Continuing to "unroll" the recursion,
this is 5 * (4 * (3 * factorial(2))), which in turn unrolls to
5 * (4 * (3 * 2 * factorial(1))). This in turn evaluates to
5 * (4 * (3 * (2 * (1 * factorial(0))))), which finally gives
5*(4*(3*(2*(1*1))), or 5*4*3*2*1, which is 120.
*/

/*
// Using nat instead of int doesn't work here
//
function method fact'(n: nat): nat
{
    if n==0 then 1 else n * fact(n-1)
}
// (n-1) violates the non-negativity of the nat 
// type when n is 0 (a valid nat value). Dafny
// often catches subtle problems of this kind,
// that might escape the notice of a mere human
// programmer.
*/



/* 
Computes the sum of all of the integers from 
zero up to given non-negative integer, n. 
*/
function method sum(n: int): int 
    requires n >= 0
{
    if (n == 0) then 0 else n + sum(n-1)
}



/*
Implements addition using recursive application
of increment-by-one. To add x and y, this function 
applies the increment (inc) function x times to y. 
The value of x is restricted to non-negative values 
so that the recursion is guaranteed to terminate.
Be sure you really understand this example.
*/
function method add(x:int, y: int): int
    requires x >= 0
{
    if (x==0) then y else inc(add(x-1, y))
}


/*
Finally, here's a Main method written in imperative
style. It applies the functions we developed above
to arguments to perform simple "smoke tests" to see
if each function produces the expected results for
at least one set of arguments. 
*/
method Main()
{
    print "The value of id_int(3) is ", id_int(3), "\n";
    print "The value of square(3) is ", square(3), "\n";
    print "The value of inc(3) is ", inc(3), "\n";
    print "The value of fact(5) is ", fact(5), "\n";
    print "The value of sum(5) is ", sum(5), "\n";
    print "The value of add(4,5) is ", add(4,5), "\n";
}

