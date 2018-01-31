include "imperative.dfy"

method Main()
{
    var fac5 := factorial(5);
    print "The (wrong) factorial of 5 is ", fac5, "\n";
    var vfac5' := verified_factorial(5);
    print "The (right) factorial of 5 is ", vfac5', "\n";
    var fib5' := fibonacci(5);
    print "Fibonacci 5 is ", fib5', "\n";
}
