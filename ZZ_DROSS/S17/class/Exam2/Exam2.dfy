/*
You should be able to compile and run this file as is.
Your task is to modify it by replacing "stub" code with
working code at each point indicated in the following
instructions. Running the cede as provided should give
you four lines of output with 0 numbers for each line.
Once you confirm that the code runs, you can proceed to
"make it work". Make backups of your code as you go in
case of problems with VS Code or anything else.
*/

method Main()
{
    var S := {1, 2, 3};
    var stub: set<(nat,nat)> := {};

    /*
    Replace the stub with a set comprehension expression
    that evalutes to the product set of S with itself. 
    */
    var prod := stub;


    /*
    Replace the stub with a set comprehension expression
    that evalutes to the set of all binary relations on 
    s. Hint: use "prod" in your expression. Replace the 
    0 in the following print statement so that it prints 
    the number of binary relations on S.
    */
    var rels := stub;


    /*
    
    */
    print "The # of relations is ", 0,  "\n";


    /*
    Give a mathematical formula for the number of binary 
    relations on a finite set with cardinality, n.

    Answer here: 
    */

    
    /*
    NOTE: To complete the remaining questions in this section, 
    first implement the set theoretic predicate methods that 
    follow this Main() routine. Each take a set of natural
    numbers, S, and a set pairs of natural numbers, R, meant
    to represent a binary relation on S. You should implement
    those methods before completing the rest of this section.
    Note: We are *not* using the binRelOnS class here.) 
    */
    
    /*
    Replace the stub with a set comprehension expression
    so that parts represents the set of partial functions 
    on S. Hint: Take advantage of your definition of rels
    and your definitions of set theory predicates, below.
    Fix the print statement so it prints out the number
    of such functions on S.
    */
    var parts := stub;
    print "The # of partial functions is ", 0,  "\n";


    /*
    Replace the stub with a set comprehension expression
    so that tots represents the set of total functions
    on S.
    */

    var tots := stub;
    print "The # of total functions is ", 0,  "\n";


   /*
    Replace the stub with a set comprehension expression
    so that bijs represents the set of bijections on S.
    */

    var bijs := stub; 
    print "The # of bijections is ", 0,  "\n";


    /*
    Give a mathematical expression for the number of
    bijections on a set of cardinality n. Hint: vary 
    the size of S between 0 and 4 and see if you can
    see the pattern. Even better, think about what it
    means to be a bijection. What do you get when
    you apply a bijection to each element of a set?
    
    Your answer here:

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

    }
/*
Replace the stubbed-out body of this defintion with 
a predicate (a proposition about S and R) that states 
that if there is a pair (x, y) in R then both x and y 
have to be in S. This is the condition that has to
be true of S and R for R to properly represent a
binary relation on S. This predicate is used as a 
precondition in each of the following functions.
Hint: You'll need to use universal quantification.
*/
predicate isValid(S: set<nat>, R: set<(nat,nat)>)
{
    false
}

/*
Replace the body of this defintion with a predicate
that states that the relation is total, in the sense
that the relation is defined for every value in S.
Hint: Use universal and existential quantifiers.
*/
function method isTot(S: set<nat>, R: set<(nat,nat)>): bool 
    requires isValid(S, R);
{
    false
}


/*
Replace the body of this definition with a predicate
that expresses that the relation R is a function on S.
*/
function method isFun(S: set<nat>, R: set<(nat,nat)>): bool
    requires isValid(S, R);
{
    false
}

/*
Modify this this definition to expresses that the 
relation R is both a function and that it is surjective.
Make "being a function" a precondition.
*/
function method isSurj(S: set<nat>, R: set<(nat,nat)>): bool
    requires isValid(S, R)
{
    false
}

/*
Modify this this definition to expresses that the 
relation R is both an injective function. Make "being 
a function" a precondition.
*/
function method isInj(S: set<nat>, R: set<(nat,nat)>): bool
    requires isValid(S, R)
{
 false
}

/*
Modify this this definition to expresses that the 
relation R is a bijection. Make "being a function" 
a precondition. Do not (directly) use quantifiers
in your answer.
*/
function method isBij(S: set<nat>, R: set<(nat,nat)>): bool
    requires isValid(S, R)
{
    false
}
