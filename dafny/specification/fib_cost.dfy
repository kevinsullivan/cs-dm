/*
  base case #1: cost(0) = 1
  base case #2: cost(1) = 1
  recursive case: cost(n) = 1 + cost(n-1) + cost(n-2)

*/

function method fib_cost(n: nat): nat
{
    if (n==0) then 1
    else if (n==1) then 1
    else 1 + fib_cost(n-1) + fib_cost(n-2)
}

method Main()
{
    print fib_cost(30), "\n";
}