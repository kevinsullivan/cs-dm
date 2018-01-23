/*
Type synonyms. Sometimes you want to use a more meaningful
name for an existing type. For example, you might want to 
have a type called "numberOfPoints" that's really just a 
nat, but with a name that better communicates the intended
interpretation and use of the type. In such cases, you can
use a "type synonym."
*/

// A type synonym declaration has no terminating semicolon

type numberOfPoints = nat
method UseOfTypeSynonym() 
{
    var winningScore: numberOfPoints := 101;
}

/* 
Note that "string" is basically a type synonym
for seq<char>. Type synomyms can be polymorphic,
too. Here's an example where we give the type 
name Graph<T> to a type that is a pair, with a
first element being a set<T> and the second 
being a map (binary relation!) from T to T.
It's not a perfect definition because there's
noth that restricts the map to have edges that
connect elements of the set, but the example
gets the point across.
*/

type Graph<T> = (set<T>, map<T,T>)

method GraphPlay()
{
    var g: Graph<int> := ({1,2,3}, map[1:=1, 1:=2, 2:=3, 3:=2]);
}


// Classes!

class C {
    var f: int
    method Example() returns (b: bool)
    {
        b := f == this.f;
    }
}

method ClassPlay() {
    var c := new C;
    var b := c.Example();
}

/*
Data members initially have unspecified values of their
respective types. It's thus common to define initialization
member functions. Such functions must not return any values
and must modify nothing other than the current object (this).
The modifies clause states and enforces this restriction.
Unlike in Java, C++, etc., you can name initializers as
you wish.
*/
class D {
    var f: int
    method myInitializer(x: int) 
        modifies this;
    {
        this.f := x;
    }
 }

 method InitPlay()
 {
     var d: D := new D.myInitializer(5);
 }

 /*
 Constructor methods are special initialization
 methods. If or more more are declared, then one
 must be used whenever an object is created; and
 these methods can only be used at object creation
 time. They're like constructors in C++ and Java.
 They can be named, and one can be unnamed.
 */

 class E {
    var f: int
    constructor init(x: int) 
        modifies this;
    {
        this.f := x;
    }
    constructor (x: int)
        modifies this
        {
            this.f := x;
        }
 }

 method ConstructorPlay()
 {
     var e1 := new E.init(5);
     var e2 := new E(5); // calls anonymous ctor
 }

/*
There more to Dafny, but for now you have 
what you need to write functional, imperative, 
and object-oriented code and specifications.
We'll introduce additional capabilities as we
go.
*/