/*
(c) Kevin Sullivan. 2018.
*/

include "binRelOnS.dfy"
include "binRelOnST.dfy"

module compose_test
{
    import opened binRelS
    import opened binRelST

    method nameMajorSchool()
    {
        print "*** NAME MAJOR SCHOOL ***\n\n";
        
        var names := { "Jane", "Binh", "Larry" };
        var majors := { "BACS", "BSCS", "EnvSci" };
        var name_major := { ("Jane","BACS"), ("Binh","BSCS"), ("Larry", "EnvSci") };
        var nameToMajor :=
            new binRelOnST<string,string>(names,majors,name_major);
        assert nameToMajor.isFunction() && nameToMajor.isTotal();
        // Is this specification valid vs. reality?
        assert forall n :: n in names ==> nameToMajor.isDefinedFor(n);

        var schools := { "SEAS", "CLAS" };
        var major_school := { ("BACS","CLAS"), ("BSCS","SEAS"), ("EnvSci","CLAS") };
        var majorToSchool := 
            new binRelOnST (majors, schools, major_school);
        assert majorToSchool.isFunction() && majorToSchool.isTotal();
        // What about this specification?

        print "NAMES:\n", names, "\n";
        print "MAJORS:\n", majors, "\n";
        print "SCHOOLS:\n", schools, "\n";
        print "NAME-MAJOR RELATION:\n", nameToMajor.rel(), "\n";
        print "MAJOR-SCHOOL RELATION:\n", majorToSchool.rel(), "\n";

        var nameToSchool := nameToMajor.compose(majorToSchool);
        print "NAME-SCHOOL RELATION:\n", nameToSchool.rel(), "\n";
    }

    method fof()
    {
        print "\n\n*** FRIENDS OF FRIENDS ***\n\n";

        var people :=  { "Jane", "Binh", "Larry", "Spiros" };
        var friends := { ("Jane","Binh"), ("Binh","Larry"), ("Larry", "Spiros") };
        var friendsRel := new binRelOnS(people, friends);
        var friendsRel' := friendsRel.compose(friendsRel);
        print "\nFriendsRel2:\n", friendsRel'.rel(), "\n";
        // we'd like to be able to take unions of relations
        // exercise -- in class
        // might as well define relation equality while we're at it
    }

    method Main()
    {
        nameMajorSchool();
        fof();
    }
}
