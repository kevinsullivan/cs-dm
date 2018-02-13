method Main() 
{
    /* BLOCK

    In Dafny, you can make one bigger
    command from a sequence of smaller
    ones by enclosing the sequence in
    braces. You typically use this only
    for the bodies of loops and the parts
    of conditionals.
    */

    {
        print "Block: Command1\n";
        print "Block: Command2\n";
    }

    /* BREAK

    The break command is for prematurely 
    breaking out of loops
    */
    var i := 5;
    while (i > 0)
    {
        if (i == 3) 
        { 
            break;
        }
        i := i - 1;
    }
    print "Break: Broke when i was ", i, "\n";

    /* Update ("Assignment")

    There are several forms of the update command. The first is 
    the usual assignment that you see in many languages. The
    second is "multiple assignment", where you can assign several
    values to several variables at once. The final version is not
    so familar. It *chooses* a value that satisfies some property
    and assigns it to a variable.
    */

    var x := 3;         // typical assignment
    var y := 4;         // typical assignment  
    print "Update: before swap, x and y are ", x, ", ", y, "\n";
    x, y := y, x;       // one-line swap using multiple assignment
    print "Update: after swap, x and y are ", x, ", ", y, "\n";
    var s: set<int> := { 1, 2, 3 }; // typical: assign set value to s
    var c :| c in s;    // update c to a value such that c is in s
    print "Update: Dafny chose this value from the set: ", c, "\n";


    /* VAR: variable declaration

    A VarDeclStatement is used to declare one or more local 
    variables in a method or function. The type of each local 
    variable must be given unless the variable is given an initial 
    value in which case the type will be inferred. If initial values 
    are given, the number of values must match the number of 
    variables declared. Note that the type of each variable must be 
    given individually. This "var x, y : int;" does not declare both 
    x and y to be of type int. Rather it will give an error 
    explaining that the type of x is underspecified.
    */

    var l: seq<int> := [1, 2, 3]; // explicit type (sequence of its)
    var l'          := [1, 2, 3]; // Dafny infers type from [1, 2, 3]


    /* IF -- conditionals

    There are several forms of the if statement in Dafny. 
    The first is  "if (Boolean) block-statement." The second is
    "if (Boolean) block-statement else block-statement" A block
    is a sequence of commands enclosed by braces (see above).

    In addition, there is a multi-way if statement similar to a
    case statement in C or C++. The conditions for the cases are
    evaluated in an unspecified order. The first to match results
    in evaluation of the corresponding command. If no case matches
    the overall if command does nothing.
    */

    if (0==0) { print "If: zero is zero\n"; }   // if (bool) {block}
    if (0==1) 
        { print "If: oops!\n"; } 
    else 
        { print "If: oh good, 0 != 1\n"; }

    var q := 1;
    if {
        case q == 0 => print "Case: q is 0\n";
        case q == 1 => print "Case: q is 1\n";
        case q == 2 => print "Case: q is 2\n";
    }


    /* WHILE -- iteration
    
    While statements come in two forms. The first is a typical Python-like statement "while (Boolean) block-command". The
    second involves the use of a case-like construct instead of
    a single Boolean expression to control the loop. This form
    is typically used when a loop has to either run up or down
    depending on the initial value of the index. An example of
    the first form is given above, for the BREAK statement. Here
    is an example of the second form.
    */

    var r: int;
    while
        decreases if 0 <= r then r else -r;
    {
        case r < 0 => { r := r + 1; }
        case 0 < r => { r := r - 1; }
    }

    /*
    Dafny insists on proving that all while loops and all
    recursive functions actually terminate -- do not loop
    forever. Proving such properties is (infinitely) hard
    in general. Dafny often makes good guesses as to how to
    do it, in which case one need do nothing more. In many
    other cases, however, Dafny needs some help. For this,
    one writes "loop specifications." These include clauses
    called "decreases", "invariant", and "modifies", which
    are written after the while and before the left brace
    of the loop body. We discuss these separately, but in 
    the meantime, here are a few examples.
    */

    // a loop that counts down from 5, terminating when i==0. 
    i := 5;                 // already declared as int above
    while 0 < i             
        invariant 0 <= i    // i always >= 0 before and after loop
        decreases i         // decreasing value of i bounds the loop
    {
        i := i - 1;
    }

    // this loop counts *up* from i=0 ending with i==5
    // notice that what decreases is difference between i and n
    var n := 5;
    i := 0;
    while i < n
        invariant 0 <= i <= n
        decreases n - i
    {
        i := i + 1;
    }


    /* ASSERT - prove property of state at point in execution

    Assert statements are used to express logical proposition that 
    are expected to be true. Dafny will attempt to prove that the 
    assertion is true and give an error if not. Once it has proved 
    the assertion it can then use its truth to aid in following 
    deductions. Thus if Dafny is having a difficult time verifying a 
    method the user may help by inserting assertions that Dafny can 
    prove, and whose true may aid in the larger verification effort.
    (From reference manual.)
    */

    assert i == 5;      // true because of preceding loop
    assert !(i == 4);   // similarly true
    // assert i == 4;   // uncomment to see static assertion failure


    /* PRINT -- produce output on console

    From reference manual: The print statement is used to print the 
    values of a comma-separated list of expressions to the console. 
    The generated C# code uses the System.Object.ToString() method 
    to convert the values to printable strings. The expressions may 
    of course include strings that are used for captions. There is 
    no implicit new line added, so to get a new line you should 
    include “\n” as part of one of the expressions. Dafny 
    automatically creates overrides for the ToString() method for 
    Dafny data types. 
    */

    print "Print: The set is ", { 1, 2, 3}, "\n"; // print the set


    /* RETURN ()

    From the reference manual: A return statement can only be used 
    in a method. It terminates the execution of the method. To return a value from a method, the value is assigned to one of the named return values before a return statement. The return 
    values act very much like local variables, and can be assigned 
    to more than once. Return statements are used when one wants to
    return before reaching the end of the body block of the method. 
    Return statements can be just the return keyword (where the 
    current value of the out parameters are used), or they can
    take a list of values to return. If a list is given the number 
    of values given must be the same as the number of named return 
    values.

    We illustrate the use of return at the end of this program.
    */
    return;
}
