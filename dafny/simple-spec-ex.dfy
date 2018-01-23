


// ********************************************
// ********************************************
// ********************************************

/*
   Now just for fun, let's see a few simple examples
   of Dafny specifications and of its fully automated
   verification capabilities.
*/


 // What's the bug? without a spec,
 // correctness is all in your mind.
 // Lack of a spec means anything goes!
method Abs(x: int) returns (y: int)
{
   if (x >= 0) { y := x; } else { y := x; }
}

// Even a partial specification, if explicit
// and checkable, can be helpful in revealing
// bugs
method Abs2(x: int) returns (y: int)
    ensures y >= 0
{
   if (x >= 0) { y := x; } else { y := x; }
}

/* A postcondition is a property that must be
   true of the state of a program after a given
   method runs, provided that the precondition,
   if any, way satisfied to begin with. In short,
   if the precondition for a program is true of 
   the program state and if you run the program 
   then (so long as the program terminates!) the 
   postcondition must be true of the state after
   the program runs. We often write something like
   this: "pre-condition { program } post-condition"
   to assert this proposition. Verification often 
   boils down to proving that such a proposition
   is true. You can see here that Dafny is really
   all about automatically checking whether code
   satisfies given pre/post specifications. It's
   very cool. 
*/



method foo()
{
    // var a: array<int>;
    var a := new int[10];
    var x := Find(a,12);
    x := BetterFind(a,12);
}

method Find (a: array<int>, n: int ) returns (element: int)
{
    element := a[n];
}

method BetterFind (a : array < int >, key : int ) returns ( element : int )
    requires a != null && 0 <= key < a.Length
{
    return a[key];
}