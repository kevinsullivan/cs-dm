include "functional.dfy"
import func = functional

/*
Here's an imperative program for computing factorial.
*/
method factorial(n: int) returns (f: int) 
    requires n >= 0
    ensures f == func.fact(n)
{
    if (n==0) 
    { 
        f:= 1; 
        return;
    }
    var t := n;
    var a := 1;
    while (t !=  0)
        invariant a * func.fact(t) == func.fact(n)
    {
        a := a * t;
        t := t - 1;
    }
    f := a;
}