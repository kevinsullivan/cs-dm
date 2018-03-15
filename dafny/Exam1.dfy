/*

CS8524 Spring 2018 -- Exam 1

INSTRUCTIONS: To take this exam, you MUST BE PRESENT IN CLASS. Open this file in VSCode Dafny. It should verify. Answer the questions below then save this file and submit it to Collab. BE SURE TO SAVE THE FILE TO YOUR HARD DRIVE BEFORE SUBMITTING IT. In fact, be sure to save it a few times as you go! When you're done. 

DEADLINE: 10:45AM per Collab. Do not bet against the clock:. Submit your file at least a few minutes ahead of the deadline. You can then resubmit it up until the deadline. Failure to submit before the deadline will result in a 10 point penalty. If you miss the deadline (don't do it), email your file to Sullivan@Virginia.EDU. 


This is an individual exam. No communication or collaboration of any kind is permitted, except with the instructor. You may use your notes and/or any other written materials available to you to complete this exam.
*/


/*

1. Briefly (using a simple phrase or at most one sentence for each part) define the following terms, being sure to make the distinct meanings of these terms clear:

Requirements:


Specification:


Implementation:
*/


/*
2. Requirements and specification can be and often are expressed using a "natural language,"" such as English. There are several major problems with using natural language for this purpose. Name and briefly explain at east two key problems with natural language as a language for requirements and specifications:

Answer here: 

*/



/*
3. Briefly explain why imperative languages aren't good languages for writing requirements and specifications.



*/

/*
4. Formal specifications are written in the languages of mathematical logic. Why isn't mathematical logic a good languages for writing implementations.



*/




/*
5. Neither imperative nor logical languages alone is sufficient for the rigorous engineering of software. In practice, then, a combination of logical specifications and imperative implementations is required. 



A. The activity of demonstrating that an imperative program meets a specification expressed in the language of mathematical logic is called by what technical name? 



B. Provide a mathematical specification of the real square root operation by completing this partial answer: Forall x in R (the real numbers) a real square root of x in R is any number y in R __________________.



C. Name and briefly desribe an algorithm (that would be implemented in an imperative language) for computing square roots. Details of the algorithm need not be described but the overall algorithmic approach should be described.

Answer:



D. Compare and contrast the computational complexity (how long it takes to compute an answer for an input of a given size) of a doubly recursive implementation of the Fibonacci function (as we saw in class) with that of an imperative implementation using a while loop. 

Answer:

*/


/*
6. A mathematical-logic-based (or "formal") specification of a method is typically given as a pair of predicates, or conditions, on program states. The first expresses what must be true of the state of the program when the method is called. The second expresses what must be true of the state of the program after the method completes, provided the first predicate was satisfied when the method was called.


A. What technical names are used for these two predicates?


B What keywords in Dafny are used to introduce the expression of these predicates?


C. When a method has a specification that include both kinds of predicates, Dafny checks to be sure of two things. First, it checks the code of the method itself is such that if the first condition is satisfied on entry to the method, then the method terminates and the second condition will be satisfied when the method terminates. What else does Dafny check?



*/





/*
7. Program verifiers, such as Dafny, generate, but generally hide the details of, proofs of that programs satisfy their mathematical-logic specifications. What Dafny tries to prove, for example, is that if a program is called in a valid state, then no matter what *path* it takes when executing (e.g., through branches and loops), it will end up in a state that always satisfies its specification. While much of the proof-generating activity is automated, verifiers do need human assistance when it comes to loops.


A. Why do loops pose problems for verifiers?



B. What are the assertions called that have to be given as loop specifications to enable a verifier such as Dafny to "reason about" (prove) whether or not the state after a loop terminates is correct?



C. Such an assertion together with an additional fact after a loop executes must  imply that a correct result has been obtained. What is that other fact?


*/



/*
8. Briefly explain in plain simple English what function this recursive functional program computes. Hint, the program implements a predicate on the natural numbers. That is, it returns true or false thereby indicating whether a given number has a particular propery. What property is it?

function method mystery(n: nat): bool 
{
    if n==0 then  false
    else if (n==1) then true
    else mystery(n-2)
}

Answer here (a few words at most): 

*/



/*
9. In just a few words explain what is wrong with each of the following two recursive programs. For part B, give an example input that causes a malfunction.


A.
function method bad(n: nat): nat
{
    bad(n)
}

Answer: 


B.
function bad_fact(n: int): int
{
    if n==0 then 1 else
    n * bad_fact(n-1)
}

Answer: 

*/



/*
10.  TO START, YOU MUST UNCOMMENT THE "ENSURES" AND THE 
"ASSERT" AFTER THE WHILE LOOP IN THE FOLLOWING METHOD. 
THE PROGRAM WILL THEN NOT VERIFY.

This method defines a function in an imperative style that
uses iterated addition to compute the product of natural
numbers, n and m. It uses a loop to add m to 0 n times. 

Provide the missing loop invariant to enable Dafny 
to verify that this program satisfies its specification. 
The missing invariant goes where the comment in the code
indicates it should go.

You will know you have a good answer when the assertion
after the while loop verifies. The assertion *is* true.
It's just that Dafny can't prove it without that extra
piece of logic that you must provide.

If you're unable to get a correct answer, comment out
the ENSURES and the ASSERT so that you can compile this
file if needed for other parts of the exam.


*/

method x(n: nat, m: nat) returns (prod: nat)
    //ensures prod == n * m;    // UNCOMMENT THIS LINE
{
    var i : nat:= n;
    var a: nat := 0;
    while (i > 0)
        // YOUR ANSWER GOES HERE
    {
        a := a + m;
        i := i - 1;
    }
    //assert a == n * m;  // UNCOMMENT THIS LINE
    prod := a;
    return;
}



/*
11. Here are three sets: A = { 1, 2 }, B = { "X", "Y" }, C = { 1, 3 }. 

A. What sets do the following expressions represent? Write each answer 
using display notation (just as in the question here).


*. What is the product set, A X C?


*. What is the set A minus the set C


*. What is the intersection of A and C


*. What is the union of A and C?


*. Can Dafny compute the union of A and B? If so, what is the result? If not
why not?


B. What is the cardinality of A union C?


C. What is the cardinality of the powerset of A union C?


D. Recall that a relation is any subset of a product set. How many relations are there from A to B? 


*/


/*
12. The following questions require you to write a few short bits of Dafny code.
Such code has to be written inside a method, so we provide a Main method within
which you should write your code. You may include print statements and compile 
and run this file, if you wish, to check your answers, though this is not required.
*/


method Main()
{
    /*
    Define a Dafny variable, s1, to have as its value the set { 1, 2, 3 }. Use
    display notation.
    */

    

    /*
    Define a Dafny variable, s2, to have as its value the set of natural numbers from 0 to 999,999 (inclusive). 
    */

    

    /*
    Define a Dafny variable, c1, to have as its value the cardinality of s2.
    */

    

    /*
    Define a Dafny variable, ps1, to have as its value the powerset of s1. Use
    comprehension notation.
    */

    

    /*
    This question as you to define a binary relation, ri, on ps1, 
    represented as a set of pairs. Bear in mind that ps1 is a set 
    of sets, namely all of the subsets of s1. The elements of ri 
    will therefore be pairs of sets. The relation, ri, is to have
    as its elements every pair of subsets, (ss1, ss2), where ss1 
    is a subset of ss2. For example, the pairs, ({}, {1,2,3}) and 
    ({1,2}, {1,2}), will be in the set of pairs because in each
    case, the first set is a subset of the second subset; but the
    pair ({1}, {}) is not in ri.
    */

    

}



/*
13. Is the "ri" relation from the last question a function? Briefly justify your
answer. If your answer is no, provide a counter-example that proves your point.


*/




/*
14. Consider two sets, A = { 1, 2 } and B = { 1, 2, 3 }.

* Give a set of pairs from A X B that constitutes an injective function from A to B.


* Give a set of pairs from A X B that constitutes a non-injective function from A to B.


*. Give a set of pairs from A X B that constitutes a relation on A and B but that is not a function. Briefly explain why your set of pairs cannot represent a function.


*/



/*
Extra Credit.

Give a set of pairs from { 1, 2, 3 } X { 1, 2, 3 } that is reflexive and transitive. Each value, 1, 2, and 3, must appear in at least one tuple in your relation. Recall that reflexivity requires that something be true of every element of the set, so the empty relation won't do as an answer here.




*/
