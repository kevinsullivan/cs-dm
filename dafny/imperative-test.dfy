include "imperative-factorial.dfy"
include "imperative-fibonacci.dfy"
import opened impfac = imperative_factorial;
import opened impfib = imperative_fibonacci;

method Main()
{
    var fac5 := factorial_unverified(5);
    print "The (wrong) factorial of 5 is ", fac5, "\n";
    var vfac5' := factorial_verified(5);
    print "The (right) factorial of 5 is ", vfac5', "\n";
    var fibu5000' := fibonacci_unverified(5000);
    print "Fibonacci 5000 is ", fibu5000', "\n";
    var fibv5000' := fibonacci_verified(5000);
    print "Fibonacci 5000 is ", fibv5000', "\n";
}
