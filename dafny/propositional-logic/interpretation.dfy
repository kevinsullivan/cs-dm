 include "syntax.dfy"

 module interpretation
 {
    import opened syntax

   /*
    We define an "interpretation" that maps our
    Boolean variables to corresponding (bool) values. 
    In programming languages, such a mapping from
    variables to values is called an environment. 
    Another term for the same idea is "state." The
    state of a program is the value of each of its
    variables at a given point in program execution.
    
    We represent an interpretation as a Dafny map
    from our own Boolean variables to Dafny bool 
    values: i.e., map<bVar,bool>. 
    
    When we need to evaluate a variable expression, 
    we'll  look up the value of the variable in such
    a map. 

    To make the purpose of this particular type of
    map clear, we define a "type synonym," namely 
    "pInterpretation." From this point on, instead 
    of writing map<bVar, bool> we use the synonym.
    Type synonyms don't change the behavior of code
    in any way, but they can make the intent of the 
    code clearer to human readers. In this sense,
    they support a form of "abstraction", hiding 
    complex details behind a more meaningful name.
    */

    type pInterpretation = map<pVar, bool>

    /*
    We note that a map might not be "total": that
    is, it might not contain an entry for every 
    variable (bVar) we have declared to exist. If
    we try to look up a value that is not defined
    in the map, we'll get an error. For example, if
    i is an interpetation (a map<string, bool>) and
    we try to look up the bool value for a string
    that isn't defined in the map, e.g., "FooBar",
    it won't work.

    Our solution for now will be to define a function
    that takes an interpretation and a string to look
    up and that returns the value for the string in the
    map if it's defined in the map, and that returns
    the value "false" as a default if the string is 
    not in the map. 
    
    This isn't a great design, in that a return of 
    "false" could mean one of two things: either the 
    value of the variable really is false, or it's 
    just not assigned a value in the interpretation. 
    For now, our design is good enough to illustate 
    our main points.
    */

    function method pVarValue(v: pVar, i: pInterpretation): bool
        //    requires v in i
    {
        //    i[v]
        if (v in i) then i[v] else false
    }

    method show_pInterps(interps: seq<pInterpretation>, vs: seq<pVar>)
    {
        var i := 0;
        print "{\n";
        while (i < |interps|)
        {
            show_pInterp(vs, interps[i]);
            if i < |interps| - 1 { print ",\n"; }
            i := i + 1;
        }
        print "\n}\n";
    }

    method show_pInterp(vs: seq<pVar>, interp: pInterpretation)
        //requires forall v :: v in vs ==> v in interp
    {
        var n := | vs |;
        var i := 0;
        print "[";
        while (i < n) {
            match vs[i] 
            {
                case mkPVar(s:string) => 
                    if vs[i] in interp {
                        print s, " := ", interp[vs[i]], ", ";
                    }
            }
            i := i + 1;
        }
        print "]";
    }

    /*
    Given a sequence, vs, of Boolean variables, return a 
    sequence of all (2^|vs|) possible interpretations, i.e.,
    mappings from these variables to Boolean values. Watch
    out: for large numbers of variables the result be very
    large.
    */
 }

    /*************** 

    function method init_interp'(vs: seq<pVar>): pInterpretation
    {
        init_interp'_helper(vs, map[])
    }



    function method init_interp'_helper(vs: seq<pVar>, i: pInterpretation): (p: pInterpretation)
        // ensures forall v :: v in vs ==> v in p
    {
        if | vs | == 0 
        then i
        else init_interp'_helper(vs[1..], i[vs[0] := false])
    }


    function method next_interp'(vs: seq<pVar>, a: seq<pInterpretation>): pInterpretation
        requires | a | >= 1;
    {
        increment_interp'(vs, a[0], | vs |)
    }


    function method  increment_interp' (vs: seq<pVar>, i: pInterpretation, idx: nat): pInterpretation
        requires 0 <= idx < |vs|
        requires forall v :: v in vs ==> v in i
    {
       if idx == 0 then i 
       else if vs[idx] !in i then i
       else if i[vs[idx]] == false then i[ vs[idx] := true ]
       else increment_interp'(vs, i[ vs[idx] := false ], idx - 1)
    }

    function method all_interps'(vs: seq<pVar>): (result: seq<pInterpretation>)
    {
        all_interps'_help(vs, pow2(|vs|), [ init_interp'(vs) ])
    }

    function method all_interps'_help(vs: seq<pVar>, fl: nat, a: seq<pInterpretation>):
        (result: seq<pInterpretation>)
            requires | a |  >= 1;
    {
        if fl == 0 
        then a  
        else all_interps'_help(vs, fl - 1, [ next_interp'(vs, a)] + a )     
    }
}
    */