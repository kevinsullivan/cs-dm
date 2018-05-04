method Main()
{
    var S := {1, 2 };
    /*
    Replace the {} with a set comprehension expression
    that evalutes to the product set of s with itself. 
    */
    var prod := set x, y | x in S && y in S :: (x, y);
    /*
    Answer: prod is the set of (x,y) pairs such that x
    is in S and y is in S.
    */


    /*
    Replace the {} with a set comprehension expression
    that evalutes to the set of all binary relations on 
    s. Hint: use "prod" in your expression.
    */
    var rels := set R | R <= prod;
    /*
    Answer: A binary relation on a set is a subset of 
    the product set of the set with itself. We define
    rels to be the set of all R's such that R is any
    subset of prod (the product set of S with itself).
    */

    /*
    Replace the 0 in the following print statement so
    that it prints the number of binary relations on s.
    */
    print "The # of relations is ", |rels|,  "\n";
    /*
    The cardinality of a set, A, is denoted |A|, in 
    both ordinary mathematical writing and in Dafny.
    That is the expression needed here to make this
    code work independent of the (for any) value of S.
    */

    /*
    Give a mathematical formula for the number of binary 
    relations on a finite set with cardinality, n.

    Answer here:  The number of relations on a set,
    S, is the cardinality of the power set (set of
    all subsets) of the product set of S and itself.
    If |S| = n, the cardinality of the product set
    of S and itself is n^2, and the cardinality of
    the powerset of the product set is 2^(n^2).
    */

    /*
    To complete the remaining questions in this section, you
    should first implement the set theoretic predicate methods
    that follow this main routine. Each take a set of natural
    numbers, S, and a set pairs of natural numbers, R, meant
    to represent a binary relation on S. You should implement
    those methods before completing the rest of this section.
    Note: We are *not* using the binRelOnS class here.) 
    */
    
    /*
    Replace the {} with a set comprehension expression
    so that tots represents the set of partial functions 
    on S. Hint: Take advantage of your definition of rels
    and your definitions of set theory predicates, below.
    Fix the print statement so it prints out the number
    of such functions on S.
    */
    var parts := set R | 
        R in rels && isFun (S, R);
    print "The # of partial functions is ", |parts|,  "\n";
    /*
    We'll take two answers here: consistent with binRelOnST, 
    we'll also take set R | R in rels && isFun (S, R) && 
    !isTot(S,R). Mathematicians differ on the meaning of the
    term, partial function: some include all functions, some
    mean only the "strictly" partial functions, which is what
    we formalized in binRelOnST.
    */


    /*
    Replace the {} with a set comprehension expression
    so that tots represents the set of total functions
    on S.
    */


    var tots := set R | 
        R in rels && isFun (S, R) && isTot(S,R);
    print "The # of total functions is ", |tots|,  "\n";

   /*
    Replace the {} with a set comprehension expression
    so that tots represents the set of bijections on S.
    */
    var bijs := set R | 
        R in rels && isFun(S, R) && isBij(S, R);
    print "The # of bijections is ", |bijs|,  "\n";


    /*
    Give a mathematical expression for the number of
    bijections on a set of cardinality n. Hint: vary 
    the size of S between 0 and 4 and see if you can
    see the pattern. Even better, think about what it
    means to be a bijection. What do you get when
    you apply a bijection to each element of a set?
    
    Your answer here: n!

    Small extra credit: Give a mathematical expression
    for the number of possible orderings (shufflings) of
    a deck of 52 cards: 

    Technical note: If you try to run this code
    with a set of size 5 or greater, it might well
    crash owing to the largish number of relations 
    involved and the blow-up in memory requirements 
    involved in translating Dafny programs into the 
    form required for analysis by Dafny's SAT (to 
    be technical, SMT) solver, Z3.
    */

    /*
    Answer: n!  A bijection on a set and itself is
    basically a permutation. Think of a list of nats
    from 1 to n. Any re-ordering of such a list is a
    "permutation". When you're re-ordering, there are
    n ways to pick the first element in the new order,
    n-1 ways to pick the second element, n-2 ways to
    pick the third elements, all the way to the end,
    where is is only one choice left. The number of
    ways to reorder is thus n * (n-1) * ... * 1, or
    n!
    */

    }
/*
Replace the body of this defintion with a predicate
(a proposition involving S and R) that states that 
if there is a pair (x, y) in R then both x and y 
have to be in S. This is the condition that has to
be true of S and R for R to properly represent a
binary relation on S. This predicate is used as a 
precondition in each of the following functions.
Hint: You'll need to use universal quantification.
*/
predicate isValid(S: set<nat>, R: set<(nat,nat)>)
{
    forall x, y :: (x, y) in R ==> x in S && y in S
}
/*
Answer (S, R) is a valid representation of a relation,
R, on S, if every value in every pair in R is also in
S. That's what the specification here says.
*/

/*
Replace the body of this defintion with a predicate
that states that the relation is total, in the sense
that the relation is defined for every value in S.
Hint: Use both universal and existential quantifiers.
*/
function method isTot(S: set<nat>, R: set<(nat,nat)>): bool 
    requires isValid(S, R);
{
    forall x :: x in S ==> 
        exists y :: y in S && (x, y) in R   
}
/*
For every x in S there has to be a y in S such that
(x,y) is in R.
*/


/*
Replace the body of this definition with a predicate
that expresses that the relation R is a function on S.
*/
function method isFun(S: set<nat>, R: set<(nat,nat)>): bool
    requires isValid(S, R);
{
    forall x, y, z :: x in S && y in S && z in S ==>
        (x, y) in R && (x, z) in R ==> y == z
}
/*
To be a function, a relation must be single-valued. That is,
for any x, y, and z in S,, the only way for (x,y) and (x,z) 
to be in R is for y=z.
*/

/*
Modify this this definition to expresses that the 
relation R is both a function and that it is surjective.
Make "being a function" a precondition.
*/
function method isSurj(S: set<nat>, R: set<(nat,nat)>): bool
    requires isValid(S, R) && isFun(S, R)
{
    forall y :: y in S ==> 
        exists x :: x in S && (x, y) in R   
}
/*
We add isFun(S,R) as a precondition. The bijectivity
requirement then says that for every y in r, there is
some x such that (x,y) is in R. The function is also
said to be "onto".
*/

/*
Modify this this definition to expresses that the 
relation R is both an injective function. Make "being 
a function" a precondition.
*/
function method isInj(S: set<nat>, R: set<(nat,nat)>): bool
    requires isValid(S, R) && isFun(S, R)
{
    forall x, y, z :: x in S && y in S && z in S ==>
        (x, z) in R && (y, z) in R ==> x == y       
}
/*
We make isFun(S, R) a precondition. Recall that injective
means that the function is one-to-one and *not* many-to-one.
That is, for all x, y, and z in S, the only way for (x, z)
and (y, z) to both be in R is if they're the same, i.e., 
x = y.
*/

/*
Modify this this definition to expresses that the 
relation R is a bijection. Make "being a function" 
a precondition. Do not (directly) use quantifiers
in your answer.
*/
function method isBij(S: set<nat>, R: set<(nat,nat)>): bool
    requires isValid(S, R) && isFun(S, R)
{
    isInj(S,R) && isSurj(S,R)      
}
/*
Explanation: Software systems are built in layers of
abstraction. Having already defined isInj and isSurj,
we can just use them here. The trick, however, is to
ensure that the preconditions of those functions are
satisfied at this call site. That means that we have
to make sure that when the functions are called, Dafny
knows they are functions. We add isFun as a precondition
here; and that makes sense anyway, as bijectivity is a
property of functions, in particular, and not of
binary relations more generally.
*/
