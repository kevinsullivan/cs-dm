/*
Equality.
*/

predicate set_eq<A(!new)>(S: set<A>, T: set<A>)
{
    forall x :: x in S <==> x in T
}

/*
Subset.
*/
predicate set_subseteq<A(!new)>(S: set<A>, T: set<A>)
{
    forall s :: s in S ==> s in T
}

/*
Proper Subset.
*/
predicate set_subset<A(!new)>(S: set<A>, T: set<A>)
{
    forall s :: s in S ==> s in T && (exists t :: t in T && t !in S)
}

function foo(): set<int>
{
    set t: int | 0 <= t <= 50 && t % 2 == 0
}

function intersection<A>(S: set<A>, T: set<A>): set<A>
{
    set e | e in S && e in T
}

function union<A>(S: set<A>, T: set<A>): set<A>
{
    //set e | e in S || e in T
    {}
}

function set_minus<A>(T: set<A>, S: set<A>): set<A>
{
    set e | e in T && e !in S
}

function method set_product<A,B>(S: set<A>, T: set<B>): set<(A,B)>
{
    set s, t | s in S && t in T :: (s,t)
}