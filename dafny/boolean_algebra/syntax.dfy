module expression
{
    /*
        In this module, we define the *syntax* of 
        a little language of Boolean expressions without
        variables. The language we define here provided
        Boolean *literal* expressions and connectives 
        (and, or, not, implies) for composing smaller
        Boolean expressions into larger ones.
    */
    
    /*
        The fundamental discrete mathematics concept
        that this unit introduces is that of "inductive
        data type definitions." We define the syntax of 
        our Boolean expression language as an *inductive
        data type*.
    */

    /*
        An inductive data type defines a set of values:
        namely the values (or "terms") of the type. For
        example, the values of an inductively defined 
        *bool* type might be *true* and *false*. Every 
        value of an inductive type has exactly one type.
        
        An inductive data type definition provides a set
        of *constructor* functions for building values of
        the given type. A constructor takes zero or more 
        arguments, possibly including values of the type
        being defined, and "packages up" its arguments 
        into a tuple of argument values labelled with 
        the name of the constructor. 
        
        A constructor that takes no arguments creates a
        term that is just the name of the constructor:
        a labelled zero-tuple, if you want to think of 
        it that way.  
        
        In our example of a *bool* type, the values *true*
        and *false* are thus provided by two parameterless
        constructors, named *true* and *false*. Such terms 
        are the "smallest", or "base", terms, of a type.

        The fact that a constructor of a type can take 
        arguments, including arguments of the same type,
        allows "larger" terms/values of the type to be 
        "built up" from smaller values of the same type.
        In this module, we use this idea to define the
        syntax of a language of expressions by providing
        constructors that allow smaller expressions to be
        composed into larger expressions. 

        As an example from Boolean algebra, *true* is an
        expression, and *false* is an expression, but so 
        is *true and false*. The latter is an example of 
        a larger expression built from two smaller ones
        using what we might call an "and" constructor that
        takes two arguments of the same *bool* type. It
        can thus combine arbitrarily large expressions
        into an even larger one. 
        
        The values of an inductive type include all (and
        only) the values that can be constructed by any
        finite number of applications of constructors. It
        is thus possible in our little *bool* example to
        build terms of arbitrarily large but always still
        finite size. 

        Now we see how we can use these ideas to 
        provide a type that defines the *syntax* 
        of a simple language of Boolean expressions.
        Expressions are the values of this type! The 
        base values are literal expressions, which 
        we call *bTrue* and *bFalse* to distinguish
        these *expressions* from the Boolean values,
        *true* and *false* themselves. We provide
        one additional constructor for each logical
        connective: and, or, not, and implies, by
        which we can build larger expressions from
        smaller ones. 
    */


    /*
    Here's the actual inductive data type definition.
    It's introduced by the keyword, "datatype". Then
    comes the name of the type we're defining, "bExp"
    (for Boolean EXPression), followed by an equals
    sign and then a list of constructors for the type
    separated by vertical bar (aka "pipe") characters.
    Each constructor has a name and an optional list
    of named arguments. Note the arguments in this
    case are of the very type that is being defined.
    */
    datatype bExp = 
        bTrue |
        bFalse | 
        bNot (e: bExp) |
        bAnd (e1: bExp, e2: bExp) |
        bOr (e1: bExp, e2: bExp) | 
        bImpl (e1: bExp, e2: bExp)


    /*
    This type is the essential content of this module.

    We now define a few useful functions for converting
    expressions of this type into strings so that we can
    print them out. 
    
    The fundamental concept introduced here is the idea 
    that when given a value of this type we can take it
    apart by "matching" it with the constructor and the
    set of arguments that was used to build it. To do this
    we use a "match" expression.

    Constuctor expressions build values up from parts.
    Match expressions take them apart (destructure them)
    and hand us the "pieces", telling us what constructor 
    and what arguments were used so that we can work with 
    them.
    
    In particular, given a larger expression, we will be
    able to figure out what constructor was used to build
    it, i.e., whether it's an "and" expression, an "or"
    expression, etc., and what small smaller expressions 
    were used to build the larger one.  

    We build up larger values inductively, and then we 
    take them apart recursively, with such a recursion
    terminating when we reach "base" values of the type.
*/

    /*
    Here then is a method to convert a bExp to a string. It
    uses the  fundamental concept of "destructuring" a value 
    of an inductively defined type by matching it against the
    constructor used to create it, extracting the arguments 
    that were passed to the constructor, and then recursively 
    generating a string to represent the constructor that was
    used along with recursive calls to produce strings for 
    the sub-expressions that were used as arguments to the
    given constructor. The recursion terminates with code
    that generates strings for the "base" values of the type.
    */
    function method show_bExp(e: bExp): string
    {
        match e 
        {
            /* 
            Print the base expression, bTrue and bFalse,
            as the strings, "True" and "False" respectively.
            */  
            case bTrue => "True"
            case bFalse => "False"

            /*
            For inductively constructed terms, determine
            the constructor that was used, print out a
            corresponding string and then recursively 
            generate strings for the subexpressions that
            were given as arguments to the constructor.
            Add parentheses around and commas between the
            strings for the subexpressions.
            */
            case bNot (e': bExp) => 
                "NOT (" + show_bExp(e') + ")"
            case bAnd (e1: bExp, e2: bExp) => 
                "AND (" + show_bExp(e1) + ", " + show_bExp(e2) + ")"
            case bOr (e1: bExp, e2: bExp) =>  
                "OR (" + show_bExp(e1) + ", " + show_bExp(e2) + ")"
            case bImpl (e1: bExp, e2: bExp) =>  
                "-> (" + show_bExp(e1) + ", " + show_bExp(e2) + ")"   
        }
    }

    /*
    This function returns a string representing the given
    Boolean expression using "infix" notation. That is,
    rather than putting the Boolean operator names before
    their arguments, it puts them in between. It inserts
    parenthesis "with abandon" to disambiguate the order
    of operations in complex expressions.
    */
    function method show_bExp_infix(e: bExp): string
    {
    match e 
        {
            case bTrue => "True"
            case bFalse => "False"
            case bNot (e: bExp) => 
                "(Not " + show_bExp_infix(e) + ")"
            case bAnd (e1: bExp, e2: bExp) => 
                "(" + show_bExp_infix(e1) + " AND " + show_bExp_infix(e2) + ")"
            case bOr (e1: bExp, e2: bExp) =>  
                "(" + show_bExp_infix(e1) + " OR " + show_bExp_infix(e2) + ")"
            case bImpl (e1: bExp, e2: bExp) =>  
                "(" + show_bExp_infix(e1) + " -> " + show_bExp_infix(e2) + ")"        
        }
    }
}