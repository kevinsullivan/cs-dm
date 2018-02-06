include "functional.dfy"
module specifications 
{
    import opened functional

   /*
    A a formal specification is basically a proposition 
    about certain values in a program. But there is an
    important sublety. The problem is that the truth of 
    such a proposition does not depend on the values of 
    any variables *other than those* referred to in the 
    proposition. For example, the truth of an assertion 
    that (x == 0) does not depend on the value of any 
    variable other than x.

    When it comes to specifying postconditions, this 
    is a bit of a problem. Consider, for example, a
    postcondition for a method in a class with an int
    field, x, that requires only that the method sets
    the new value of x to its original value plus one.
    We write this in Dafny as (x == old(x) + 1). The x 
    on the left refers the value of x after the method
    runs (the new value of x), while old(x) refers to 
    its value when the method first starts to run. The
    problem is that thhis proposition will be true of
    any program that does increment the value of x, no
    matter what else it does! It could change every
    other value in the program, launches missiles, and
    shut down the power grid, and it would nevertheless
    satisfy its specification. 
    
    That is usually not what's intended. When we read
    a formal specification that requires a method to
    to increment x, we generally assume that there is
    an implicit additional piece of specification that
    says "and nothing else changes." So a specification
    that requires x to be incremented is usually meant
    to require that x be incremented and that nothing
    else be changed.

    To specify the desired behavior would thus require
    propositions of the form "the new value of x is the
    old value plus one, and for every other object, o,
    in the program, o == old(o)," that is, the desired
    effect is achieved and nothing else changes.

    So, for example, if a method of a class with two
    fields, x and y, has an explicit postcondition that
    requires x to be incremented, then it would generally 
    be assumed that there's also an implicit postcondition 
    that y == old(y), i.e., that "x will be incremented 
    and nothing else changes. The intended postcondition
    is thus really (x == old(x) + 1) && y == old(y).

    If there were dozens of variables other than x, it
    would be inconvenient to have to write these "does
    not change" postconditions for each of them. What
    Dafny therefore does is to implicitly impose such a
    postcondition for every variable that it not listed
    as being subject to change. The modifies clause in
    Dafny is thus used in effect to remove one or more
    of these "does not change" postconditions, allowing
    a method to change a value. 

    In the following example, we have a class with two
    fields, x and y, and a method that's meant to change
    x but not y. We therefore must list the x field of 
    the class, denoted as this`x, as being potentially
    modified by the execution of the method. If we left
    out this clause, we'd get an error where a new value
    of x is assigned. Similarly, if we added y := 0 to
    the body of the program, we'd get an error letting
    us know that y is not allowed to be modified. If we
    want to allow a method to change all fields of the
    class, we could just say "modifies this."
    */

    class ModifiesExample
    {
        var x: int;
        var y: int;

        method Change()
            modifies this`x;
            ensures x == old(x) + 1;
        {
            x := inc(x);
        }
    }

    /*
        This example illustrates several features
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

        Third, this example illustrates a modifies clause. 
        A subtle aspect of a formal specification is that it
        allows any effects that it doesn't explicitly rule 
        out. So, for example, if a postcondition requires 
        only that x == old(x), which is to say that the 
        value of x, doesn't change, then any program that 
        leaves the value of x unchanged would satisfy the 
        specification, even if it changed every other value 
        in the program. The modifies class indicates which
        values are permitted to be changed, thus implicitly
        specifying that, for every other value, v, that v
        is not changed. In a sense, then, a modified clause
        implicitly adds v == old(v) as a postcondition for
        every value not designated in the modifies clause.
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
