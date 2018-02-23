/*
Specification and implementation of Spivey's
famous "Birthday Book" example of a Z formal
specification. See the Z Reference Manual or 
related paper for original source.  
*/

module birthday_book
{
    /* 
    Concrete types for names and dates.
    Here represent dates simply as ints.
    Would want to fix that in a useful
    version.
    */

    type name = string;
    type date = int;

    class birthday_book
    {
        /*
        A class defines a new abstract data type.
        An abstract data type comprises a set of
        *abstract* values and a set of operations
        involving values of these abstract types.

        This class provides an abstraction of a
        birthday book, to which name/birtday pairs
        can be added, in which know names can be
        matched to their birthdays, and in which
        a birthday can be matched with the set of
        known names having that birthday.
        */
        var known: set<name>;
        var birthday: map<name,date>;

        /*
        A "predicate" representing the
        "state invariant" for objects of
        this type. A name is in the set,
        known, if and only if there is
        a birthday registered for that
        name in the "birthday" book.
        */
        function Valid(): bool
            reads this;
        {
            forall n :: n in known <==> n in birthday
        }


        /*
        This method adds a name/birthday pair
        to the birthday book. The name must not
        already be known, and in that case, the
        method ensures that the "known" set is
        updated by the addition of the name
        and the "birthday" map is updated with
        the given name|->date tuple (and nothing
        else changes). In general, this method
        does change "this" object. In Dafny, the
        "modifies this" is what allows for such
        changes to be made.
        */
        method addBirthday(n: name, d: date)
            requires Valid();
            requires n !in known;
            ensures known == old(known) + { n }
            ensures n in known && n in birthday && birthday[n] == d;
            modifies this;
            ensures Valid();
        {
            known := known + { n };
            birthday := birthday[ n := d ];
        }

        /*
        Given a name that, required to be known,
        this method returns the corresponding
        birthday. This method is guaranteed, by
        the absence of a "modifies this" clause
        not to change the state of this object.
        */
        method findBirthday(n: name) returns (d: date)
            requires Valid();
            requires n in known;
            ensures d == birthday[n];
            ensures Valid();
        {
            return birthday[n];
        }

        /*
        Given a birthday, d, this method returns
        the set of names in the subset of names
        that are known and that have birthday, d.
        This method cannot change "this" object.

        The critical components of this method are
        its specification and the loop invariant 
        that allows Dafny to verify that the code
        satisfies the specification. The spec says
        that the returned result is exactly the 
        set of names, "n", such that "n" is in 
        "known" and "n" has birthday "today." 
        */
        method Remind(today: date) returns (names: set<name>)
            requires Valid();
            ensures names == set n | n in known && birthday[n] == today;
            ensures Valid();
        {
            /*
            Start by noting that we can't do a simple 
            "lookup" using the birthday map, as it maps
            in the wrong direction. It returns dates given 
            names, not names given dates. To find  names 
            with a given birthday, we have to do a search. 
            That is, we'll have to look at each name in 
            turn look up its corresponding birthday, and 
            add it to a set of results if the birthday 
            for that name match with the given birthday.

            Our algorithmic strategy will be to iterate over
            the elements of the "known" set. We will initialize
            a set, "left", to be "known". We use "left" as a 
            name, as the value of this set will represent the
            subset of names that are "left" to be checked. On
            each executio of the while loop body, if the name
            currently being checked has the given birthday
            we add that name to an initally empty result set, 
            "acc", and iterate, with the name just checked
            now removed from the set that is "left" to be
            checked. The loop is done when there is no more
            work "left" to do. 

            For Dafny to verify that our program satisfies
            its specification, it needs a loop invariant.
            Figuring out what the loop invariant should be
            is usually the most "interesting" part of getting
            loops right.

            Our invariant is that, no matter how many times
            the loop body has executed, the set of names with 
            birthdays today (the result we seek) is the set 
            of names that we've already selected as having a 
            birthday today (the result of the work already
            done, represented in the value of "acc") combined 
            with the set of names with birthdays today that
            remain in the set that is still "left" to be
            checked. 
            
            Given this invariant, and using just a little bit
            of logical reasoning, it's clear that when the 
            the loop is finished, there will be no work left, 
            and so all of the names with birthdays today will
            *have to be* in the "acc" set. The loop *forces*
            the answer that we seek to end up in "acc". 

            To pronounce the loop invariant in English, we'd
            say, "no matter how many times the loop body runs
            (that's the meaning of "invariant") the set of 
            names that are known AND with birthdays today" is
            the union of two sets: the subset of names that
            are "left" to be checked AND that have birthdays
            today, and the set of names that we have already
            found (in the set of known names) with birthdays 
            today.
            */
            var left := known;
            var acc := {};
            while (left != {}) 
                decreases left;
                invariant 
                    (set n | n in known && birthday[n] == today) == 
                        (set n | n in left && birthday[n] == today) +
                        (set n | n in acc)
            {
                var n :| n in left;
                if (birthday[n] == today) { acc := acc + { n }; }
                left := left - { n };
            }
            return acc;
        }


        /*
        In Dafny, "predicate" is shorthand for
        "a pure function that returns a Boolean
        value indicating whether some state of
        affairs holds." This predicate specifies
        the state of affairs that we will require
        to hold when "this" object is constructed.
        In particular, the set of known names and
        the map from names to birthdays are both
        empty.
        */
        predicate Init()
            reads this;
        {
            known == {} && birthday == map[]
        }

        /*
        This class has one constructor. In Dafny, 
        a constructor called "constructor" with no
        arguments is called implicitly when one
        uses "new" to create a class instance with
        no explicitly constructor call. 

        The specification of this constructor is
        critically important. It requires that 
        a fresh new object of this type satisfy
        the Init predicate, and thereby also 
        satisfy the "representation invariant."

        Now here's the intelelctual magic trick:
        if we know that any new object satisfies 
        the representation invariant, and that 
        every method execution *preserves* the
        invariant, then we can conclude by way
        of "inductive reasoning" that the class,
        or representation, invariant must always
        hold.

        If the programming langauges prevents
        direct access to state variables (here
        "known" and "birthday") then one can be
        sure that there's *no way* to violate 
        the "integrity" of the representation.
        This idea is absolutely fundamental in
        program design: if you're careful and
        your programming languages provides
        the right mechanisms, then you can be
        absolutely certain that "abstractions"
        cannot be violated no matter what you
        do to an object.
        */
        constructor()
            ensures Init();
            ensures Valid();
        {
            known := {};
            birthday := map[];
        }
    }


    /*
    Finally, here's an example of code that
    creates and uses an instance of our class.
    Try changing it
    */
    method Main()
    {
        var bb: birthday_book := new birthday_book();
        assert bb.Valid();
        bb.addBirthday("John", 25);
        bb.addBirthday("Mike", 20);
        bb.addBirthday("Susan", 20);
        var b20 := bb.Remind(20);
        var jbd := bb.findBirthday("John");
        print "John's birthday is on day ", jbd, "\n";
        print "The people with birthdays on the 20th are ", b20, "\n";
    }
}