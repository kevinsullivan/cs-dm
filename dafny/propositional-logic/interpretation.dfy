 include "expression.dfy"

 module interpretation
 {
    import opened expression

   /*
    We define an "interpretation" that maps our
    variables to corresponding (bool) values. The
    word, "interpretation" is generally used in 
    logical discourse. In programming languages, 
    it might be called an environment. You can also
    think of it as the "memory" in which values of
    our Boolean variables will be stored.

    We represent an interpretation as a Dafny map
    from string names to Boolean values. Such a
    map is written as "map<string,bool>". When we
    need to evaluate a variable expression, we'll
    just look up the value of the variable in such
    a map. 

    To make the purpose of this particular 
    map<string, bool> clear, we give this type a
    "type synonym," namely "interp." From this point
    on, instead of writing map<string, bool> we can
    instead just write "interp".
    */

    type pInterp = map<pVar, bool>

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

    function method lookup(v: pVar, i: pInterp): bool
    {
        if (v in i) then i[v] else false
    }

    method show(vs: seq<pVar>, interp: pInterp)
    {
        var n := | vs |;
        var i := 0;
        print "[";
        while (i < n) {
            match vs[i] 
            {
                case mkVar(s:string) => 
                    if vs[i] in interp {
                        print s, " := ", interp[vs[i]], ", ";
                    }
            }
            i := i + 1;
        }
        print "]";
    }

    function method pow2(n: nat): (r: nat)
        ensures r >= 1
    { 
        if n == 0 then 1 else 2 * pow2(n-1) 
    }

    /*
        Return an interpretation for the variables in 
        the sequence vs such that every variable maps 
        to false.
    */
    method init_interp(vs: seq<pVar>) 
        returns (result: pInterp)
    {
        // start with an empty map
        result := map[];

        // iterate through variables in vs
        var i := 0;
        while (i < | vs |)
        {
            // for each one, add a maplet from it to false
            result := result[ vs[i] := false ];
            i := i + 1;
        }

        // that's it
        return result;
    }

    /*
    Takes a sequence of variables and an interpretation
    (meant to be) for those variables, and computes the
    "next" interpretation for those variables. It does this
    by in effect treating the sequence of values as a 
    binary integer and by incrementing it by one.
    */
    method next_interp(vs: seq<pVar>, interp: pInterp) 
        returns (result: pInterp)
    {
        result := interp;
        var i := | vs | - 1;
        while (i >= 0 ) 
        {
            // should be able to get rid of this with precondition
            if (! (vs[i] in interp)) { return; }
            assert vs[i] in interp;

            // The first time we find a 0, make it 1 and we're done
            if (interp[ vs[i] ] == false) 
            { 
                result := result[ vs[i] := true ];
                break; 
            } 
            else
            {
                result := result[ vs[i] := false ];
                // 1 + 1 = 0 plus a carry, so keep looping
            }

            i := i - 1;
        }
        return result;
    }

    /*
    Given a sequence, vs, of Boolean variables, return a 
    sequence of all (2^|vs|) possible interpretations, i.e.,
    mappings from these variables to Boolean values. Watch
    out: for large numbers of variables the result be very
    large.
    */
    method all_interps(vs: seq<pVar>) 
        returns (result: seq<pInterp>)
    {
        result := [];
        var interp := init_interp(vs);
        var i: nat := 0;
        var n := pow2(|vs|);
        while (i < n)
        {
            result := result + [interp];
            interp := next_interp(vs, interp);
            i := i + 1;
        }
        return result;
    }

 }  
 