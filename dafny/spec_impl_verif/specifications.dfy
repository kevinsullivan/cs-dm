include "int_nat_func_specs.dfy"
module specifications 
{
    import opened functions

   /*
    The so-called "framing problem" in specifications
    is the problem of saying what does *not* change
    when an operation is applied to an object of some
    type. The solution to this problem in Dafny and 
    in many related systems is to require specifiers
    to say what *can* change, with an assumption that
    anything not specified as being changeable cannot
    change.  

    In the following example, we have a class with two
    fields, x and y, and a method that's meant to change
    x but not y. We therefore must list the x field of 
    the class, denoted as this`x, as being potentially
    modified by the execution of the method. If we left
    out this clause, we'd get an error where a new value
    of x is assigned. If we want to allow a method to
    change all fields, we use "modifies this."
    */

    class ModifiesExample
    {
        var x: int;
        var y: int;

        method Change()
            modifies this`x;
            ensures x == old(x) + 1;
            // implicit: y must *not* be modified
        {
            x := inc(x);
            // try modifying y to see what happens
        }
    }

    /*
        The next example illustrates several features
        of Dafny. First, it introduces a class, here
        called SwapExample. This class defines a new
        type of objects, each of which has two fields,
        x and y of type int, and an associated method,
        Swap, that can be applied to any object of this
        type. This method has the effect of swapping
        the values of the x and y fields of the object
        to which the method is applied.

        Next, this example illustrates the specification
        of a postcondition that relates the initial and
        final values of given variables. In particular, 
        it requires that the value of x when the method
        completes be the value that y had when the method
        started to run, denoted as old(y), and that the
        value of y when the method completes be the value
        that x had when the method started to run, again
        denoted using the old construct.

        We can now see that a modifies clause implicitly 
        adds v == old(v) as a postcondition for every
        value not designated in the modifies clause.
    */
    class SwapExample
    {
        var x: int;
        var y: int;

        method Swap()
            ensures x == old(y) && y == old(x);
            modifies this;
        {
            /*
            // buggy!
            x := y;
            y := x;
            */

            /*
            // works
            var t := x;
            x := y;
            y := t;
            */

            // works and elegant
            x, y := y, x;
        }
    }
}
