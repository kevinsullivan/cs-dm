module expression
{
    /*
        Now we define the *syntax* of a little language 
        of Boolean expressions.
    */


    /*
    We define an infinite set of "variables" as
    terms of the form mkVar(s), and of type, BVar.
    */

    datatype Bvar = mkVar(name: string) 

    /*
    This code introduces the use of "inductive data
    type definitions." The Bvar type 

    This type has one "constructor," called mkVar.
    It takes one argument, s, of type string. The
    result of applying mkVar to a string, such as
    "P", is simply a "term" written `mkVar("P")'.

    You can think such a term as a box, labelled 
    "mkVar," and containing the string, "P", as 
    its first and only contained value. 
    
    For our purposes here, the term, mkVar("P"), 
    is the way we write "a boolean variable, P"
    in our little language.
    */

    function method bvar_name(b: Bvar): string 
    {
        match b
        {
            case mkVar(s: string) => s
        }
    }

    /* 
    This code introduces the concept of "matching" 
    on a value of an inductive type. If you think 
    of a term of an inductive type as just a box, 
    labelled with the name of a constructor, and 
    containing the values passed to the constructor
    when the term was created, then what "match" 
    does is first to figure out what constructor 
    was used to build the term. There is one case
    for each constructor. The Bvar type has only 
    one constructor so the match has only one case
    to check. Having figured out which constructor
    was used, it the gives names to the values that
    the "box" contains, which are just the values
    that were passed to the constructor when it was
    used to create the term. Finally, on the right
    of the =>, it defines what to do in the given
    case. 

    So, here, the matching unboxes the mkVar term,
    gives the name, "s" to the string it contains,
    for purposes of writing the code to the right
    of the => only, and then simply evalutes to s.

    In object-oriented programming lexicon, this
    function would be referred to as an inspector
    or accessor method. A mathematical name for it
    is a "projection" function. It "projects" the
    "s" out of the box and hands it to the client.
    */

    /********************/

    /*
    We use the definition of the syntax of Boolean expressions
    to introduce the fundamental concept of inductive definitions.
    Inductive definitions of often infinite sets of values is done
    by first defining a set starting values (like base cases for a
    recursion) and then by defining rules for forming new values 
    from ones already defined. In languages with "inductive types" 
    new types of values can be defined inductively. Concepts to discuss include: the datatype keyword, type names, "generic" type parameters (none in this example), constructor names and
    arguments, and constructors that takes parameters of the very type being defined (the "inductive" part of a definition.)
    */
    datatype Bexp = 
        // literal expressions
        litExp (b: bool) | 

        // variable expressions
        // example: varExp(mkVar("P"))
        varExp (v: Bvar) | 

        // operator application expression
        // example: notExp(varExp(mkVar("P")))
        notExp (e: Bexp) |
        andExp (e1: Bexp, e2: Bexp) |
        orExp (e1: Bexp, e2: Bexp)


    /************************/


    /*
    The rest of this module implements two methods,
    one of which returns the *set* of variables in a
    given expression, and the other of which converts
    that set into a sequence and returns it. It is 
    much easier to work with sets when collecting
    the variables in an expression, as we don't want
    to include a variable more than once. But some 
    of the code that uses this module will need an
    ordered collection, i.e., a sequence, of all the
    variables, so we provide a function for that, too.
    */

    /*
    First, given a Bexp, return a *set() containing all 
    and only the variables that appear in the expression. 
    A set contains a given element at most one time, so 
    even if a variable appears multiple times in a given
    expression, it'll be in the resulting set only once.
    */
    function method setVarsIn(e: Bexp): set<Bvar>
    {
      /*
      Do the work by calling a helper function with an
      empty sequence as the starting value. This "design 
      pattern" is typical: one implements a call to a
      a non-recursive function (this one) that then calls 
      a recursive function with some extra arguments to
      actually do the work.
      */
      setVarsInHelper(e, {})
    }

    /*
    This recursive function adds the set of variables in a 
    given expression to the set, r, given as an argument. So, 'to get a set of the variables in a given expression call 
    this function with the expression and with an empty set. 
    This is just what the "top-level" function above does.

    This code exhibits a second fundamental algorithm design
    pattern: mutual recursion. It doesn't call itself recursively,
    but, in cases where there's more work to do, calls the top-level method (that called it). This recursive call to the top level
    computes the set of variables for the *subexpression* being
    processed. This method then combines that result with the 
    results obtained so far (represented in r) to compute the
    final answer. 
    */
    function method setVarsInHelper(e: Bexp, r: set<Bvar>): set<Bvar>
    {
        match e
        {
            // a literal expression adds no variables
            case litExp (b: bool) => r

            // a var expression adds the variable it not yet there
            case varExp (v: Bvar) => r + { v }
  
            // add, or , and not expression adds the variables below 
            case notExp (e: Bexp) => r + setVarsIn(e)
            case andExp (e1: Bexp, e2: Bexp) =>
                r + setVarsIn(e1) + setVarsIn(e2)
            case orExp (e1: Bexp, e2: Bexp) =>
                r + setVarsIn(e1) + setVarsIn(e2)
        }
    }

    /*
    This method gets the *set* of variables in a given
    expression and returns it as an ordered sequence. The
    order in which the elements will appear is undefined.
    That is, they will be in some order, but one must not
    count on there being any particular order. 
    */
    method seqVarsIn(e: Bexp) returns (result: seq<Bvar>)
    {
        // Compute the set of variables the convert to sequence
        result := setVarsToSeq(setVarsIn(e));
        return;
    }

    /*
    Compute the sequence by calling a recursive helper function
    with an initially empty sequence. This is a second example of
    the design pattern seen above.
    */
    method setVarsToSeq(s: set<Bvar>) returns (result: seq<Bvar>)
    {
        var l: seq<Bvar> := [];
        var s' := s;
        while (s' != {}) 
            decreases s';
        {
            var v :| v in s';
            l := [ v ] + l;
            s' := s' - { v };
        }
        return l;
    }
}