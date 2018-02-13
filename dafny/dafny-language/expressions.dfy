method Main()
{
    /* LITERAL EXPRESSIONS

    A literal expression is a boolean literal (true or false), a null object reference (null), an unsigned integer (e.g., 3) or real (e.g., 3.0) literal, a character (e.g., 'a') or string literal (e.g., "abc"), or “this” which denote the current object in the context of an instance method or function. We have not yet seen objects or talked about instance methods or functions.
    */

    /* IF
    If expressions first evaluate a Boolean expression and then 
    evaluate one of the two following expressions, the first if 
    the Boolean expression was true, otherwise the second one.
    Notice in this example that an IF *expression* is used on the
    right side of an update/assignment statement. There is also an
    if *statement*.
    */

    var x := 11;
    var h := if x != 0 then (10 / x) else 1;    // if expression
    assert h == 0;
    if (h == 0) {x := 3; } else { x := 0; }     // if statement 
    assert x == 3;

    /* CONJUCTION, DISJUCTION

    Conjunction and disjuction are associative. This means that
    no matter what b1, b2, and b3 are, (b1 && b2) && b3 is equal
    to (b1 && (b2 && b3)), and the same for ||. 
    
    These operators are also "short circuiting" ( left to right). That is, their second argument is evaluated only if evaluating  the first operand does not by itself determine the value of the 
    expression. (From RefMan.)

    Here's an example where short circuit evaluation matters. It
    prevents the evaluation of an undefined expressions after &&.
    */

    var a: array<int> := null;  
    /* 
    Short circuit evaluation protects against evaluation of
    a[0] when a is null. That is, the right hand expressions
    is evaluated "lazily", only of the right hand expression
    doesn't already indicate what the result should be. In this
    case, because the left hand expression is false, the whole
    expression must be false, so the right side won't ever be
    evaluated.
    */
    var b1: bool := (a != null) && (a[0]==1);


    /* SEQUENCE, SET, MULTISET, MAP

    Values of these types can be written using so-called
    "display" notations. Sequences are written as lists of
    values within square brackets, sets within braces, and
    multisets using "multiset" followed by a list of values
    within braces. 
    */
    var aSeq: seq<int> := [1, 2, 3];
    var aVal := aSeq[1];    // get the value at index 1
    assert aVal == 2;       // don't forget about zero base indexing

    var aSet: set<int> := { 1, 2, 3};   // sets are unordered
    assert { 1, 2, 3 } == { 3, 1, 2};   // set equality ignores order
    assert [ 1, 2, 3 ] != [ 3, 1, 2];   // sequence equality doesn't

    var mSet := multiset{1, 2, 2, 3, 3, 3};
    assert (3 in mSet) == true;         // in-membership is Boolean
    assert mSet[3] == 3;                // [] counts occurrences
    assert mSet[4] == 0;

    var sqr := map [0 := 0, 1 := 1, 2 := 4, 3 := 9, 4 := 16];
    assert |sqr| == 5;
    assert sqr[2] == 4;
 
    
    
    /* RELATIONAL EXPRESSIONS

    The relation expressions that have a relational operator that
    compares two or more terms and returns a Boolean result. The ==, 
    !=, <, >, <=, and >= operators are "chaining". The in and !in 
    operators apply to collection types and compute membership or 
    non-membership respectively. The !! operator represents 
    disjointness for sets and multisets. (Adapted from the reference 
    manual.) Here are just a few examples, within assert statements.
    */

    assert 3 in { 1, 2, 3 };                            // set member
    assert 4 !in { 1, 2, 3 };                           // non-member
    assert "foo" in ["foo", "bar", "bar"];              // seq member
    assert "foo" in { "foo", "bar"};                    // set member
    assert { "foo", "bar" } !! { "baz", "bif"};         // disjoint
    assert { "foo", "bar" } < { "foo", "bar", "baz" };  // subset
    assert { "foo", "bar" } == { "foo", "bar" };        // set equals


    /* ARRAY ALLOCATION

    To allocate a new array for n elements of type T 
    do this: a := new T[n]. Multi-dimensional arrays
    (matrices) are also supported. The types of these
    arrays are "arrayn<T>, where "n" is the number of
    dimensions and T is the type of the elements. All 
    elements of an array or matrix must be of the same 
    type.
    */

    a := new int[10];       // type of a already declared above
    var m: array2<int> := new int[10, 10];
    a[0] := 1;              // indexing into 1-d array
    m[0,0] := 1;            // indexing into multi-dimensional array


    /* OLD

    An old expression is used in postconditions. old(e) evaluates to the value expression e had on entry to the current method. We saw
    and example of this earlier. For an example, see the "incr" method after this Main
    */

    /* CARDINALITY

    For a collection expression c, |c| is the cardinality of c. For 
    a set or sequence the cardinality is the number of elements. For 
    a multiset the cardinality is the sum of the multiplicities of 
    the elements. For a map the cardinality is the cardinality of 
    the domain of the map. Cardinality is not defined for infinite 
    maps. F
    */

    var c1 := | [1, 2, 3] |;
    assert c1 == 3;
    var c2 := | { 1, 2, 3 } |;
    assert c2 == 3;
    var c3 := | map[ 0 := 0, 1 := 1, 2 := 4, 3 := 9] |;
    assert c3 == 4;
    assert | multiset{ 1, 2, 2, 3, 3, 3, 4, 4, 4, 4 } | == 10;

    
    /* LET

    A let expression allows binding of intermediate values to identifiers for use in an expression. The start of the let expression is signaled by the var keyword. They look like local variable declarations except the scope of the variable only extends to following expression. Adapted from RefMan.
    
    Here's an example (see the following code).

    First x+x is computed and bound to sum, the result
    of the overall expression on the right hand side of
    the update/assignment statement is then the value of 
    "sum * sum" given this binding. The binding does not
    persist past the evaluation of the "let" expression.
    The expression is called a "let" expression because
    in many other languages, you'd use a let keyword to
    write this: let sum = x + x in sum * sum. Dafny just
    uses a slightly different syntax.
    */

    assert x == 3;               // from code above
    var sumsquared := (var sum := x + x; sum * sum);  // let example
    assert sumsquared == 36;     // because of the let expression

    /* OMITTED -- notable stuff not covered in this module

    lambda expressions
    object types
    iterator types
    numeric conversion
    case
    match
    quantifier
    set comprehension
    map comprehension
    */

}

/*
OLD: an example showing the use of the old expression.
This method increments the first element of an array.
The specification ensures that the method body has this
effect by explaining that the new value of a[0] must be
the original (the "old") value plus one. The "requires"
statements are needed to ensure that the array is not
null and not zero length. The modifies command explains
that the method body is allowed to change the value of a.
*/
method incr(a: array<nat>) returns (r: array<nat>) 
    requires a != null;
    requires a.Length > 0;
    modifies a; 
    ensures a[0] == old(a[0]) + 1;  
{
    a[0] := a[0] + 1;
    return a;
}
