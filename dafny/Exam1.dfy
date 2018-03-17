/*

CS8524 Spring 2018 -- Exam 1

INSTRUCTIONS: To take this exam, you MUST BE PRESENT IN CLASS. Open this file in VSCode Dafny. It should verify. Answer the questions below then save this file and submit it to Collab. BE SURE TO SAVE THE FILE TO YOUR HARD DRIVE BEFORE SUBMITTING IT. In fact, be sure to save it a few times as you go! When you're done. 

DEADLINE: 10:45AM per Collab. Do not bet against the clock:. Submit your file at least a few minutes ahead of the deadline. You can then resubmit it up until the deadline. Failure to submit before the deadline will result in a 10 point penalty. If you miss the deadline (don't do it), email your file to Sullivan@Virginia.EDU. 


This is an individual exam. No communication or collaboration of any kind is permitted, except with the instructor. You may use your notes and/or any other written materials available to you to complete this exam.
*/


/*

1. Briefly (using a simple phrase or at most one sentence for each part) define the following terms, being sure to make the distinct meanings of these terms clear:

Requirements: Requirements defines the effects that a system is meant to have on the environment in which it will be used.


Specification: Specifications describe what behavior a system must have.


Implementation: Implementations describe how (by what procedure a system in meant to achieve its specified behavior.
*/


/*
2. Requirements and specification can be and often are expressed using a "natural language,"" such as English. There are several major problems with using natural language for this purpose. Name and briefly explain at east two key problems with natural language as a language for requirements and specifications:

Answer here: Natural language requirements and specifications are prone to ambiguity, incompleteness, inconsistency.

*/



/*
3. Briefly explain why imperative languages aren't good languages for writing requirements and specifications.

Programs written in imperative languages do not clearly communicate what behavior a program is meant to have, e.g., what function a program is meant to compute or what kind of interaction it is meant to have with its environment.

*/

/*
4. Formal specifications are written in the languages of mathematical logic. Why isn't mathematical logic a good languages for writing implementations.

Mathematical logic is (for all intents and purposes) not executable. You can't run it, at least not efficiently. A specification written in a logical notation doesn't explain *how* to compute a desired result, even if it clearly states what properties that result must have.

*/




/*
5. Neither imperative nor logical languages alone is sufficient for the rigorous engineering of software. In practice, then, a combination of logical specifications and imperative implementations is required. 



A. The activity of demonstrating that an imperative program meets a specification expressed in the language of mathematical logic is called by what technical name? 

Verification.



B. Provide a mathematical specification of the real square root operation by completing this partial answer: Forall x in R (the real numbers) a real square root of x in R is any number y in R *** such that y^2 == x ***.



C. Name and briefly desribe an algorithm (that would be implemented in an imperative language) for computing square roots. Details of the algorithm need not be described but the overall algorithmic approach should be described.

Answer: Newton's method. It iteratively updates an estimate of the square root until the result is "close enough" (judged by the difference between the argument and the estimate squared).



D. Compare and contrast the computational complexity (how long it takes to compute an answer for an input of a given size) of a doubly recursive implementation of the Fibonacci function (as we saw in class) with that of an imperative implementation using a while loop. 

Answer: The doubly recursive function takes time *exponential* in the argument, n, while the iterative method only takes time linear in n.

*/


/*
6. A mathematical-logic-based (or "formal") specification of a method is typically given as a pair of predicates, or conditions, on program states. The first expresses what must be true of the state of the program when the method is called. The second expresses what must be true of the state of the program after the method completes, provided the first predicate was satisfied when the method was called.


A. What technical names are used for these two predicates?

* pre-condition
* post-condition

B What keywords in Dafny are used to introduce the expression of these predicates?

* requires
* ensures


C. When a method has a specification that include both kinds of predicates, Dafny checks to be sure of two things. First, it checks the code of the method itself is such that if the first condition is satisfied on entry to the method, then the method terminates and the second condition will be satisfied when the method terminates. What else does Dafny check?

In addition to checking that the method body satisfies the pre-condition / post-condition specification, Dafny also checks that every call to the method satisfies the pre-condition.

*/





/*
7. Program verifiers, such as Dafny, generate, but generally hide the details of, proofs of that programs satisfy their mathematical-logic specifications. What Dafny tries to prove, for example, is that if a program is called in a valid state, then no matter what *path* it takes when executing (e.g., through branches and loops), it will end up in a state that always satisfies its specification. While much of the proof-generating activity is automated, verifiers do need human assistance when it comes to loops.


A. Why do loops pose problems for verifiers?

A verifier such as Dafny cannot reason about all possible paths through a loop, as the numbers of paths can be astronomical. 

B. What are the assertions called that have to be given as loop specifications to enable a verifier such as Dafny to "reason about" (prove) whether or not the state after a loop terminates is correct?

These assertions are called loop *invariants*



C. Such an assertion together with an additional fact after a loop executes must  imply that a correct result has been obtained. What is that other fact?

The additional fact is that when the loop terminates, the loop condition must be false. (It's the combination of the invariant and knowledge that the loop condition is false that allows one, including Dafny, to conclude that the loop did the right thing.)
*/



/*
8. Briefly explain in plain simple English what function this recursive functional program computes. Hint, the program implements a predicate on the natural numbers. That is, it returns true or false thereby indicating whether a given number has a particular propery. What property is it?

function method mystery(n: nat): bool 
{
    if n==0 then  false
    else if (n==1) then true
    else mystery(n-2)
}

Answer here (a few words at most): Is n odd?

*/



/*
9. In just a few words explain what is wrong with each of the following two recursive programs. For part B, give an example input that causes a malfunction.


A.
function method bad(n: nat): nat
{
    bad(n)
}

Answer: This recursion does not terminate (for any n).


B.
function bad_fact(n: int): int
{
    if n==0 then 1 else
    n * bad_fact(n-1)
}

Answer: This recursion does not always terminate (for any n < 0)

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
    ensures prod == n * m;    // UNCOMMENT THIS LINE
{
    var i : nat:= n;
    var a: nat := 0;
    while (i > 0)
        // YOUR ANSWER GOES HERE
        invariant a + i * m == m * n;
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

A. What sets do the following expressions represent? Write each answer using display notation (just as in the question here).


*. What is the product set, A X C?

{(1,1), (1,3), (2, 1), (2,3)}


*. What is the set A minus the set C

{2}


*. What is the intersection of A and C

{1}

*. What is the union of A and C?

{1, 2, 3}

*. Can Dafny compute the union of A and B? If so, what is the result? If not
why not?

No. Sets in Dafny must have elements all of the same time. Sets must be of the same type to apply the union operator in Dafny.


B. What is the cardinality of A union C?

3


C. What is the cardinality of the powerset of A union C?

8


D. Recall that a relation is any subset of a product set. How many relations are there from A to B? 

16 -- the number of subsets of the product set; the product set has four elements; there are 2^4 subsets; these are all of the relations on the two sets

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

    var s1 := { 1, 2, 3 };

    /*
    Define a Dafny variable, s2, to have as its value the set of natural numbers from 0 to 999,999 (inclusive). 
    */

    var s2 := set n | 0 <= n <= 999_999;

    /*
    Define a Dafny variable, c1, to have as its value the cardinality of s2.
    */

    var c1 := | s2 |;

    /*
    Define a Dafny variable, ps1, to have as its value the powerset of s1. Use
    comprehension notation.
    */

    var ps1 := set s | s <= s1;

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

    var ri := set ss1, ss2 | ss1 in ps1 && ss2 in ps1 && ss1 <= ss2 :: (ss1,ss2);

}



/*
13. Is the "ri" relation from the last question a function? Briefly justify your
answer. If your answer is no, provide a counter-example that proves your point.

No. The relation is not single-valued. There are multiple tuples with the same 
first element, including ({}, {1}) and ({}, {2}). 
*/




/*
14. Consider two sets, A = { 1, 2 } and B = { 1, 2, 3 }.

* Give a set of pairs from A X B that constitutes an injective function from A to B.

{(1,1), (1,2)} -- there are other possible answers

* Give a set of pairs from A X B that constitutes a non-injective function from A to B.

{(1,1), (2,1)} -- there are other answers


*. Give a set of pairs from A X B that constitutes a relation on A and B but that is not a function. Briefly explain why your set of pairs cannot represent a function.

{(1,1), (1,2)} -- there are other answers

*/



/*
Extra Credit.

Give a set of pairs from { 1, 2, 3 } X { 1, 2, 3 } that is reflexive and transitive. Each value, 1, 2, and 3, must appear in at least one tuple in your relation. Recall that reflexivity requires that something be true of every element of the set, so the empty relation won't do as an answer here.

{(1,1), (2,2), (3,3)} -- reflexive because every element is related to itself. It is also transitive, albeit trivially so, in that for all a, b, and c, *if* a is related to b and b is related to c then a is related to c. In this case, the only way to get from a to b and from b to c is for a, b, and c to be the same element. The fact that every element is related to itself then entails that if you can go from a to a, and from a to a, then you can go from a to a, and that makes this relation also transitive. There are other answers involving more tuples. The answer given here is the *smallest* relation that is both reflexive and transitive. Other larger relations could be correct answers, as well.


*/
