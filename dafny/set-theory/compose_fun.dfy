include "binRelOnS.dfy"
include "binRelOnST.dfy"

module compose_fun
{
    import opened binRelS
    import opened binRelST

    method Main()
    {
        var students := {"Pete", "Binh", "Anna" };
        var majors := {"BACS", "BSCS", "EnvSci" };
        var studentMajors := 
            { ("Pete","BACS"), ("Pete","EnvSci"), ("Anna", "BSCS"), ("Binh", "BACS") };
        var student2major := new binRelOnST<string,string>(students,majors,studentMajors);

        var schools := {"SEAS", "CLAS"};
        var majorSchool := 
            { ("BACS","CLAS"), ("BSCS","SEAS"), ("EnvSci","CLAS") };
        var major2School := new binRelOnST(majors,schools,majorSchool);

        var student2School := 
            student2major.compose(major2School);

        print student2School.rel();

        var friendPairs := {("Anna","Pete"), ("Pete","Binh"), ("Pete","Anna")};
        var friends := new binRelOnS(students, friendPairs);
        var mystery := friends.compose(friends);
        print "\n", mystery.rel();
    } 
}