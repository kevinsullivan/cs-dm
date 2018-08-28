/*****************
PART II: RECURSION
******************/

/* 5
Write a recursive function that
takes any natural number as an
argument and returns true if it's 
odd and false otherwise. Call your 
function, isOdd(n). A hint: 0 is 
not odd and 1 is odd. Think about 
base and recursive cases. You do
not need more than three cases.
Using an "if ... then ... else if 
... then ... else ..." is a good
idea.
*/
// your answer here
function isOdd(n: nat): bool 
{
    if n==0 then false 
    else if n==1 then true
    else isOdd(n-2)
}


/**************************************
PART III: LANGUAGE SYNTAX AND SEMANTICS
***************************************/

/*
You've studied and worked on defining
two little languages: one of Boolean
expressions, and a closely related one
of propositions in propositional logic.
To define the syntax of these languages
you used inductive data type definitions.
To define their semantics, you used an
approach we call structural recursion.
This problem tests your understanding
and ability to use these ideas to define
a syntax and a semantics for yet another 
simple language: f arithmetic expression, 
such as 1, -1, 1 + 2, etc.
*/

/* 10
We start with an inductive definition of 
part of the syntax of our little language 
of arithmetic expressions. See below. The 
language currently supports only literal
expressions, such as aLit(5), representing
the integer value, 5, and expressions built
using an addition operator, here implemented
as the aPlus constructo. Expressions thus
include aPlus(aLit(5),aLit(6)), which we'd 
ordinarily write as 5 + 6. Your task is to 
extend the grammar with two constructors: 
one for negation and one for subtraction.

First, add an "aNeg" constructor that
takes an aExp as an argument. It will
represent the unary negation operator. For 
example, the term, aNeg(aLit(5)), will be 
taken to represent the expression, -5.

Second, add an "aMinus constructor that
takes two arithmetic expressions arguments. 
The aMinus constructor will be used to 
create subtraction expressions. For example, 
aMinus(aLit(5), aLit(2)) will be taken to 
represent the expression, 5 - 2.
*/
datatype aExp =
    | aLit (n: int)
    | aNeg (e: aExp)
    | aPlus (e1: aExp, e2: aExp)
    | aMinus (e1: aExp, e2: aExp)
    | aTimes (e1: aExp, e2: aExp)


/* 10
The syntax of our language is defined 
by the inductive data type, aExp. Its 
semantics are defined by a recursive
evaluation function, aEval, that when
given any arithmetic expression (aExp)
returns the integer value it represents.
So, aEval(aMinus(aLit(5), aLit(2))),
for example, should return 3.

Now, having extended the syntax of our 
language, you will need to extend its
semantic evaluation function to account 
for the new constructors, thus defining
how expressions built using them are to
be evaluated. 
*/
function aEval(e: aExp): int
{
    match e
    {
        case aLit(n) => n
        case aNeg(e) => -aEval(e)
        case aPlus(e1, e2) => aEval(e1) + aEval(e2)
        case aMinus (e1: aExp, e2: aExp) => aEval(e1) - aEval(e2)
        case aTimes (e1: aExp, e2: aExp) => aEval(e1) * aEval(e2)
    }
}

/*
Finally, write test cases to test that the
evaluator is working for expressions built
using each of the constructors. For example,
write a test as a simple theorem stating that
aEval(aMinus(aLit(5), aLit(2))) = 3. 
*/

/*
You won't be marked off for not doing this
problem or for doing it wrong.
*/

/*
Need to wrap assertions in a Main() method.
*/
method Main() 
{
    assert aEval(aMinus(aLit(5), aLit(2))) == 3;
    /*
    Dafny verifies validity automatically, in
    effect producing a proof of the proposition.
    Yep: Dafny assertions are just propositions: 
    written in first-order predicate logic.
    */
}

/*
EXTRA CREDIT:

Write a function called aPrint that takes an
aExp as an argument and that returns a string
representation suitable for printing. Use infix
notation, in which binary operators go in between 
operands and parentheses enclose sub-expressions 
so that the order of operations is clear). Your 
code should work with your extended version of
the syntax.
*/
function method aPrint(e: aExp): string
{
    match e
    {
        case aLit(n) => toString(n)
        case aNeg(e) => "(-(" + aPrint(e) + "))"
        case aPlus(e1,e2) => "(" + aPrint(e1) + "+" + aPrint(e2) + ")"
        case aMinus(e1,e2) => "(" + aPrint(e1) + "-" + aPrint(e2) + ")"
        case aTimes(e1,e2) => "(" + aPrint(e1) + "*" + aPrint(e2) + ")"
    }
}

// this function stubbed out -- need to implement
function method toString(n: int): string
{
    "123"
}



/**************************************
PART IV: SPECIFICATION AND VERIFICATION 
***************************************/

/* 5
In Dafny, write a pure function, called id_int,
that implements the identify function on values
of type int. That is, given any integer, n, it 
just returns that very same value, n. Be sure 
that you provide a pure function, not imperative
code.
*/

function id_nat(n: int): int { n }



/*
Here is a partial implementation of an imperative
program in Dafny that is required to implement the 
identity function on the natural numbers (note the
change from int to nat), but now using imperative 
code. It does so in a silly way. 

Given an integer, n, as an argument, that satisfies
the precondition that n >= 0 (basically that it's a
nat) this program then uses a while loop to decrement 
a copy m, of n, by 1 while incrementing a variable, 
r, initialized to 0, until m = 0. Think of m as a
pile of stones initially of size n and r as pile of
stones initially of size 0, where an execution of
the loop body moves one stone from the m pile to the
r pile. When the m pile is empty the r pile should
have n stones in it. The program then returns r. 

Your task has three parts: first, add a pre-condition
requiring the value of n to be non-negative (>= 0).
Second add a post-condition to this program to ensure 
that it implements the id_int function (for values
that satisfy this function's precondition). Third, 
add a loop invariant sufficient for Dafny to verify 
that the program satisfies its post-condition.
*/

method id_nat_method(n: int) returns (r: int)
    requires n >= 0;        // 5
    ensures r == id_nat(n); // 5
{
    var m := n;     // make copy of n
    r := 0;         // initialize r
    while (m > 0)
        invariant m + r == n;   // 10
        invariant m >= 0;
    {
        r := r + 1;
        m := m - 1;
    }
    return r;
}



/*****************
PART V: SET THEORY
******************/


/* 
The problems in this section are to
be answered by adding code to or by
modifying code in the following method.
*/

method exam2()
{
    /*
    The following sets are used in 
    several problems in this section.
    */
    var S := { 1, 2, 3, 4, 5 };
    var R := {( 1, 2), (2, 3), (3,4), (5, 5) };

    /* 5
    QUESTION: Is R a binary relation on S? 
    Explain your answer briefly: yes, it's a
    subset of the product set of S with itself
    */

    
    /* 5
    QUESTION: Is R reflexive? Explain briefly:
    No, as reflexivity requires that every value
    in S be related to itself in R, and that is
    not the case here.
    */



    /* 5
    PROBLEM: Write an assertion stating that the
    relation, R, on the set, S, is not transitive.
    Finish the partial definition already given by
    replacing "false" with the right specification.
    */

    assert !forall x, y, z :: 
                    x in S && y in S && z in S ==>
                    (x, y) in R && (y, z) in R ==>
                    (x, z) in R;


    /* 5
    The reflexive closure of a relation, R, on a
    set S, is the smallest reflexive relation that 
    contains R. That sounds complicated, but what 
    it means is that the reflexive closure of R is 
    just the union of R with the set of all (x, x) 
    pairs for any x in S. Your task is two-fold.
    First, implement the reflexiveClosure function.
    Second, write a test case that tests whether
    the set of pairs it returns given S and R is
    the set of pairs that is the reflexive closure
    of R. Write out the expected set of pairs using
    display (curly braces) notation.
    */

    var rc := reflexiveClosure(S, R);
    assert rc == R + {(1,1), (2,2), (3,3), (4,4), (5,5) };
    assert rc == R + set s | s in S :: (s,s); // ok, better 
}

/* 5
Replace the {} in this code with an expression that
returns the reflexive closure of R, namely the union
of R with the set of (x,x) pairs for all x values in S.
*/
function method 
    reflexiveClosure(S: set<int>, R: set<(int,int)>): set<(int,int)>
{
    R + set x | x in S :: (x,x)
}


