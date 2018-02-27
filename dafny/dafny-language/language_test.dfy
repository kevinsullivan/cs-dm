module language_test
{
/*
A little homework exercise for you.
*/

    method Main()
    {
        set_tests();
        seq_tests();
        map_tests();
    }

    /***
    **** SETS -- unordered collections without duplicates
    ***/

 
     method set_product<T1,T2>(s1: set<T1>, s2: set<T2>) 
        returns (r: set<(T1,T2)>)
    {
        var first := s1;
        var acc : set<(T1,T2)> := {};
        while (first != {})
            decreases first;
        {
            var x :| x in first;
            var second := s2;
            while (second != {}) 
                decreases second;
            {
                var y :| y in second;
                acc := acc + { (x,y) };
                second := second - { y };
            }
            first := first - { x };
        }
        return acc;
    }

    method set_tests()
    {
    /*
        We start by declaring s1 through s8 to be variables of type "set of integers", written as set<int>. Dafny intializes set
        variables to the empty set. At the end of this module, we print the values of these sets. Check that you can compile and run this code. The output should be a bunch of empty set signifiers. We write sets as pairs of curly braces with the elements in a comma-separated list inside. The empty set
        is thus written as a pair of curly braces with no elements, as so: {}.

        Once you've confirmed that this code compiles and runs, then go through the rest of the code and add the code and answer the questions as indicated. 
        */

        var s1: set<int>;       // set is a *polymorphic* type
        var s1': set<set<int>>;
        var s2: set<int>;       // not a type per se, but rather
        var s3: set<int>;       // a sort of functiont that takes
        var s4: set<int>;       // another type as an argument
        var s5: set<int>;       // (here int) and gives you a
        var s6: set<int>;       // complete type in return
    
        var s7: set<(int,int)>; // A SET OF int-int TUPLES!!!
    
        var s8: set<int>;
        var s9: set<string>;

        // define s1 to be the set {-1, 0, 1, 2, 3}

        s1 := {-1, 0, 1, 2, 3, -1};
//        print s1;


        // define s2 to be the set { 0, 2, 4 }
        s2 := { 0, 2, 4 };

        // define s3 to be the intersection of s1 and s2
        s3 := s1 * s2; 

        // define s4 to to be the union of s1 and s2
        s4 := s1 + s2; 

        // define s5 to be the difference, s1 - s2
        s5 := s1 - s2;


        // define s6 to be the difference, s2 - s1
        s6 := s2 - s1;

        /*
        For arbitrary sets, s1 and s2, is s1 - s2 == s2 - s1?
        If they're different, in what way are they different?
        Answer here: They're different.
        */
        assert s1 - s2 != s2 - s1;


        // define s7 to be the product set, s1 * s2
        // s7 := s1 X s2;

        s7 := set_product(s1,s2);
        print "The product of ", s1, "and ", s2, " is ", s7, "\n";
    
        /*
        What kind of things are the elements of this product set?
        Answer here:
        */

        // define s8 to be the product set s2 * s1

    
        /*
        For arbitrary sets, s1 and s2, is s1 * s2 == s2 * s1?
        If they're different, in what way are they different?
        Answer here:
        */

        // Assign to a new variable c1 the cardinality of s1 * s2. 


        /*
        How does the cardinality of s1*s2 related to the cardinalities of s1 and s2 individually? Will this same relationship hold in general? If so, why; if not, 
        why not? Answer here:
        */


        /* 
        Here's a set of strings. Guess then write code to check
        the following. If you code doesn't run because it should
        not run, comment it out once you've written it.
        
        (1) Is s9 a subset of s1?
        (2) What is the cardinality of s1 * s9?
        (3) What are the elements of s1 * s9?

        */

                     
        s9 := {"Cat", "Dog", "Giraffe", "Duck", "Lizard" };

        print s1, "\n";
        print s2, "\n";
        print s3, "\n";
        print s4, "\n";
        print s5, "\n";
        print s6, "\n";
        print s7, "\n";
        print s8, "\n";
    }

    /***
    **** SEQUENCES -- ordered collections indexed by finite
    **** initial sequences of the natural numbers; we refer
    **** to the nth element of a sequence, s, of n or more
    **** elements, as s[n-1].
    ***/

    method seq_tests()
    {

        var s1 := [1,2,3,4,5];
        var s2 := [1,2,3];
        var s3 := [2,3,4,5,6];

//        print s3[2];

        /*
        Write an assertion, assert s1[?1] == s2[?2] == s3[?3],
        replacing the ?1, ?2, and ?3 with real indices so that
        (and check that) the assertion is verified. Put your 
        answer right below this comment block. Using "chaining"
        notation.
        */
         
        assert s1[2] == s2[2] == s3[1];       // <--- Right there.

        // Here's another sequence of int variable, uninitialized
        var s4: seq<int>;

        /* 
        Assign to s4 the value of an expression involving s1, so 
        that the following assertion, which you are to un-comment, is verified. The point of this exercise is to make sure you 
        understand how indexing works in sub-sequence expressions. 
        Note: assertion should show red until you get the answer.
        */
        
        s4 :=  s1[0..3];                      // <----Your code here
        assert s4 == s2;      // Uncomment this assertion



        /*
        Write an assertion here stating that s2 is a prefix of s1.
        Check and comment out if unverified an assertion that s1 is
        a prefix of s2.
        */
                      // <---- Your code here



        /*
        Write an assertion here stating that 3 is an element of s1 AND (in one assertion) that 7 is not in s2. Check if Dafny
        verifies that 3 is an element of s1 AND that 7 *IS* in s2. 
        Comment out the assertion if it does not verify.
        */
                       // <---- Your code here

        /*
        Write an assertion here stating that the length of s2 is  5.
        */
                       // <---- Your code here


        /*
        After the variable declaration here, write a command that
        assigns to s3 the values of s1 followed by that of s2. Use
        the sequence concatenation operator. Then write an assertion
        that checks that you got the right answer. You must compute
        the right answer mentally to write the required assertion.
        */
                           // update/assignment operation
                           // assertion to check that it worked


        /*
        Declare a variable cs of type "sequence of character" and initilize it to the sequence 'h', 'e', 'l', 'l', 'o'. Then assert that the sequence is equal to the string, "hello". Does Dafny accept this assertion as well formed? If not, comment it out. If so, check whether it verifies. Explain in a brief sentence why Dafny behaves as it does here.

        Explain here:
        */
                            // <-----code here   


        /*
        Declare a variable, s4, and set its value to be that of
        s1 but with the 3 "updated" to be a 7. You have to put
        together a statement that makes an assignment to s4, with
        an expression on the right involving s1 and the "update"
        operator for sequences.
        */ 
    }

    /***
    **** MAPS: sets of pairs where you can look up the second
    element of a pair by using the first element as an index. 
    ***/

    method map_tests()
    {
        /*
        Here's a map from strings to numbers, for starters,
        representing a set of students and their ages.
        */

        var ages: map<string,nat>;
        ages := map["Jane" := 9, "Lin" := 11, "Anh" := 10];
        print ages["Jane"];

        /*
        Write separate assertions to check the following claims.

        (1) There is no age for a student named "Toby" in this map.
        (2) There is an age for the student named "Jane".
        (3) Jane's age is < 12.
        (4) Lin is older than Anh.
        */
                     // <--- You code starts here


        /*
        Write a statement to print out how many people have ages
        defined in this map. Include a "new line" character after
        the output answer.
        */
                    // <--- your code here 

        
       /*
       Assign a new map to the "ages" variable obtained by updating
       the current map to increase Jane's age to 10 (she must have just had a birthday), and by adding a student to the group, "Tim," aged 11. You can do this in two steps if you wish.
       */


    }
}