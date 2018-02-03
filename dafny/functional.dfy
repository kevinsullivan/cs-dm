module functional
{

    /*
    An "identity function" for values of type nat.
    Returns whatever int value you pass to it. Note:
    the body of a pure function is not sequential 
    code operating on a memory, code but simply an 
    expression that computes a desired return value. 
    
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
    function method id_int (x: int): int { x }


    // Compute the successor of nat x. The type nat
    // is the type of integers >= 0.
    function method inc (x: int): int { x + 1 }


    // Compute the square of a given int value
    function method square (x: int): int { x * x }


    /*
     Given an int x, compute square of its successor.
     This function is implemented as a *composition*
     of the inc and square functions. It works by first
     applying inc to its argument and then applying the
     square function to that result.
     */
    function method h (x: int): int { square(inc(x)) }


    /*
     Compute the factorial of any non-negative integer.
     While you might want to think of the factorial of a
     number n as the product of the numbers from 1 to n,
     that's not perfect because we want the function to be
     defined for all natural numbers, from 0 up; and you
     can't very well define it as the product of numbers
     from 0 to n, because that would always be just zero.
     A better definition is a recursive definition. It has
     two cases: factorial of zero is one, and factorial of
     any larger number, n, is n times the factorial of the
     next smaller number, n-1. When the next smaller number
     is zero, the result is 1 and the product is then the
     product of all numbers from 1 to n. Recursion gives
     us an extremely concise way of representing functions
     such as factorial. 
     */
    function method fact(n: int): int 
        requires n >= 0
    { 
        if (n==0) then 1    // base case
        else n * fact(n-1)  // recursive case
    }
    
    
    /*
     The nat type is the type of non-negative
     integers. If we use this type, we can leave
     off the precondition, as it's already implicit
     in the nat type. We have to give our function
     a different name; and we're careful (now!) to
     make a recursive call to the new function, 
     fact', rather than to the old one!
     */

    function method fact'(n: nat): nat
    {
        if n == 0 then 1 
        else n * fact'(n-1)
    }    


    /*
    This function computes the n'th Fibonacci
    number, for any natural number, n. It directly
    implements the recursive mathematical definition
    of the function. The beauty of this code is 
    that it's runnable math. The problem is that
    it's terribly inefficient. In fact, it takes
    time exponential in n. This program makes an
    excellent specification, but a pretty lousy
    implementation of the factorial function.
    */
    function method fib(n: nat): nat
    {
        if (n < 2) then n
        else fib(n-2) + fib(n-1)
    }
    

    /* 
    Computes the sum of all of the integers from 
    zero up to given non-negative integer, n. 
    */
    function method sumto(n: nat): nat 
    {
        if (n == 0) then 0 else n + sumto(n-1)
    }

    /*
    Implements addition using recursive application
    of increment-by-one. To add x and y, this function 
    applies the increment (inc) function x times to y. 
    The value of x is restricted to non-negative values 
    so that the recursion is guaranteed to terminate.
    Be sure you really understand this example.
    */
    function method add(x:nat, y: nat): nat
    {
        if (x==0) then y else inc(add(x-1, y))
    }

    /*
    Implements exponentiation, computing m*n,
    by recursive aplication of addition of n.
    */
    function method mult(m: nat, n:nat): nat 
    {
        if (m==0) then 0
        else add(n, mult(m-1,n))    
    }

/*
   Implements exponentiation, computing m^n,
   by recursive application of our multiplation
   function.
*/
    function method exp(m: nat, n:nat): nat
    {
        if (n == 0) then 1
        else mult(m, exp(m, n-1))
    }

    function method ev(n: nat): bool
    {
        if n == 0 then true
        else if n == 1 then false 
        else ev (n-2)  
    }

    function method double(n: nat): nat{
        if n==0 then 0
        else 2 + double(n-1)
    }

    function method pred(n: nat): nat 
        requires n > 0
    {
        n - 1
    }
}


