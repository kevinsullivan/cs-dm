module birthday_book
{
    type name = string;
    type date = int;
    class birthday_book
    {
        var known: set<name>;
        var birthday: map<name,date>;

        function Valid(): bool
            reads this;
        {
            forall n :: n in known <==> n in birthday
        }

        method addBirthday(n: name, d: date)
            requires Valid();
            requires n !in known;
            ensures n in known && n in birthday && birthday[n] == d;
            modifies this;
            ensures Valid();
        {
            known := known + { n };
            birthday := birthday[ n := d ];
        }

        method findBirthday(n: name) returns (d: date)
            requires Valid();
            requires n in known;
            ensures d == birthday[n];
            // leaving out modifies ensures no changes to this
        {
            return birthday[n];
        }

        /*
        Return set of names for people whose birthday is "today"
        */
        method Remind(today: date) returns (names: set<name>)
            requires Valid();
            ensures names == set n | n in known && birthday[n] == today
        {
            /*
            Our invariant is that the complete set of names with 
            birthdays today (the result we seek) is the set of names 
            that we've already selected as having a birthday today
            (acc) combined with the set of names with birthdays today 
            in the subset of names still left to search (left). When
            the loop is finished, there will be no work left, and so
            it will be unavoidable that acc contains all names in the
            overall set with birthdays today.  
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
    }
}