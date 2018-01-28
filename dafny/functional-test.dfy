include "functions.dfy"

import func = functions

/*
Finally, here's a Main method written in imperative
style. It applies the functions we developed above
to arguments to perform simple "smoke tests" to see
if each function produces the expected results for
at least one set of arguments. 
*/
method Main()
{
    print "The value of id_int(3) is ", func.id_int(3), "\n";
    print "The value of square(3) is ", func.square(3), "\n";
    print "The value of inc(3) is ", func.inc(3), "\n";
    print "The value of fact(5) is ", func.fact(5), "\n";
    print "The value of sum(5) is ", func.sum(5), "\n";
    print "The value of add(4,5) is ", func.add(4,5), "\n";
}

