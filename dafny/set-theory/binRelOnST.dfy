module binRelST
{    
    /*
    Abstraction of a finite binary relation on a 
    set, S. Underlying representation is a triple: 
    the domain set, S, the co-domain set, T, and 
    a set of pairs over S X T.
    */ 
    class binRelOnST<S(!new,==),T(!new,==)>
    {
        var d: set<S>;      // domain: set of values of type S
        var c: set<T>       // codomain: set of values of type T
        var r: set<(S,T)>;  // relation: set of pairs from s X t
        predicate Valid()
            reads this;
        {
            // all tuple elements must be in dom and codom, respectively
            forall x, y :: (x, y) in r ==> x in d && y in c
        }

        /*
        Constructor requires that all values appearing in 
        any of the pairs in p be in domain and codomain sets,
        respectively. A note: the ensures clause really is
        needed here: the bodies of *methods* are not visible
        to the verifier, so if you want the verifier to be
        able to use knowledge of what a method does, you must
        make that behavior explicit in the specification. By
        contrast, in Dafny, function bodies are visible to 
        the verifier, though they can be made "opaque" using
        a special keyword. 
        */
        constructor(dom: set<S>, codom: set<T>, rel: set<(S,T)>)

            /*
            Ensure that all values in tuples are from dom and codom
            sets, respectively. 
            */
            requires forall x, y :: 
                (x, y) in rel ==> x in dom && y in codom;

            /*
            Explain to verifier what this method accomplishes. The
            verifier needs this information to verify propositions
            elsewhere in this code. And because method bodies are 
            "opaque" to the verifier, it can't read this information 
            from the method body itself.
            */
            ensures d == dom && c == codom && r == rel;

            /*
            Once the constructor finishes, this object should 
            satisfy its state invariant.
            */
            ensures Valid();
        {
            d := dom;
            c := codom;
            r := rel;
        }

        /*
        Return domain/range set. 
        */
        function method dom(): set<S>
            /*
            The Dafny verifier needs to know what 
            values function results depend on. So 
            we have to tell it that the function
            here can read any of the values (the
            data members) in the current function.
            */
            reads this;
            requires Valid();
            ensures Valid();
        {
            d
        }

        /*
        Return domain/range set
        */
        function method codom(): set<T>
            reads this;
            requires Valid();
            ensures Valid();
        {
            c
        }

        /*
        Return set of ordered pairs
        */
        function method rel(): set<(S,T)>
            reads this
            requires Valid();
            ensures Valid();
        {
            r
        }


        /*
        Return true iff the relation is single-valued (a function)
        */
        predicate method isFunction()
            reads this;
            requires Valid();
            ensures Valid();
        {
            forall x, y, z :: x in d && y in c && z in c &&
                            (x, y) in r && 
                            (x, z) in r ==> 
                            y == z  
        }

        
        /*
        Return true iff the relation is a function and is injective
        */
        predicate method isInjective()
            reads this;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            forall x, y, z :: x in d && y in d && z in c &&
                            (x, z) in r && 
                            (y, z) in r ==> 
                            x == y  
        }
        
        
        /*
        Return true iff the relation is a function and is surjective 
        */
        predicate method isSurjective()
            reads this;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            /*
            Compute the set of all the y's in all the (x,y) pairs
            in the relation, and see if that set is equal to t. If
            so, then there is some tuple that "hits" every y in the
            co-domain, and that's what it means to be surjective.
            */
            (set x, y | x in d && y in c && (x, y) in r :: y) == c    
        }

        /*
        Return true iff the relation a function and is bijective
        */

        predicate method isBijective()
            reads this;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            this.isInjective() && this.isSurjective()    
        }


       /*
        Return true iff the relation is total (relative to its domain)
        */
        predicate method isTotal()
            reads this;
            requires Valid();
            ensures Valid();
        {
            /*
            Compare with isSurjective. Here we compute the set of all
            the x's in all the (x,y) pairs, and if it's equal to the
            domain, s, then this function is total (defined for every
            value in s).
            */
            (set x, y | x in d && y in c && (x, y) in r :: x) == d
        }

        
        /*
        Return true iff the relation is partial (relative to its domain set)
        */
        predicate method isPartial()
            reads this;
            requires Valid();
            ensures Valid();
        {
            !isTotal()
        }


        /*
        Return true iff given "key" is in domain set.
        */

        predicate method inDomain(k: S)
            requires Valid();
            reads this;
            ensures Valid();
        {
            k in dom()
        }

        /*
        Return true iff given "value" is in cpdomain set.
        */

        predicate method inCodomain(v: T)
            requires Valid();
            reads this;
            ensures Valid();
        {
            v in codom()
        }

        /*
        Return true iff relation is defined for
        the given value. Be sure value is in domain
        before calling this function.
        */
        predicate method isDefinedFor(k: S)
            requires Valid()
            requires k in d;
            reads this;
        {
            // Check that cardinality of set of tuples with given key > 0
            k in set x, y 
                | x in dom() && y in codom() && (x, y) in rel() :: x
        }

        /*
        Return true iff given value is in range of
        relation: not just in codomain set but mapped
        to by some value for which relation is defined.
        */
        predicate method inRange(v: T)
            requires Valid()
            requires v in c;
            reads this;
        {
            v in set x, y | 
                x in dom() && y in codom() && (x, y) in rel() :: y 
        }


        /*
        Compute image set of a single value under this relation.
        */
        function method image(k: S): (vals: set<T>)
            reads this;
            requires Valid(); 
            ensures Valid();
        {
            set x, y | x in d && y in c && (x, y) in r && x == k :: y
        }


/*
        Compute image set of a set of values under this relation.
        */
        function method imageOfSet(ks: set<S>): (vals: set<T>)
            reads this;
            requires Valid(); 
            ensures Valid();
        {
            set x, y | x in d && y in c && (x, y) in r && x in ks :: y
        }

        /*
        Compute preimage set of an individual value under this relation.
        */
        function method preimage(v: S): (vals: set<T>)
            reads this;
            requires Valid(); 
            ensures Valid();
        {
            set x, y | x in d && y in c && (x, y) in r && x == v :: y
        }


        /*
        Compute preimage set of a set of values under this relation.
        */
        function method preimageOfSet(ks: set<S>): (vals: set<T>)
            reads this;
            requires Valid(); 
            ensures Valid();
        {
            set x, y | x in d && y in c && (x, y) in r && x in ks :: y
        }



        /*
        Compute image of a domain element under this relation.
        This code assumes there is exactly one element in the 
        set from which the value is drawn (but this assumption
        is not yet verified).
        */
        method fimage(k: S) returns (val: T)
            requires Valid(); 
            requires isFunction();  // ensures single-valuedness
            requires k in d;        // ensures function is non-empty
            requires isDefinedFor(k);
            //ensures this == old(this);
            //ensures d == old(d) && c == old(c) && r == old(r);
            ensures Valid();
            /*
            Make behavior of this opaque *method* visible as a spec
            */
            ensures val in set x, y | 
                x in d && y in c && (x, y) in r && x == k :: y;
        {
            var s := set x, y | 
                        x in d && y in c && (x, y) in r && x == k :: y;
            val :| val in s;
            assert |s| >= 1; // believed true but doesn't verify
        }
    }

    
    /*
    The composition, h, of two functions, f and g, where f maps 
    R-values to S-values, and g maps S-values to T-values, is
    a relation that maps R-values to T-values, where h contains
    a pair (s,r) if and only if there is some t such that (s,t)
    is in f, and (t,r) is in g. The composition of relations is
    a special case of the composition of functions. More details
    to be discussed in class.
    */
    method composeRST<R,S,T>(g: binRelOnST<S,T>, f: binRelOnST<R,S>) 
        returns (h : binRelOnST<R,T>)
        requires f.Valid();
        requires g.Valid();
        ensures h.Valid();
        ensures h.dom() == f.dom();
        ensures h.codom() == g.codom();
        ensures h.rel() == set r, s, t | 
                r in f.dom() &&
                s in f.codom() &&
                (r, s) in f.rel() &&
                s in g.dom() && 
                t in g.codom() &&
                (s, t) in g.rel() ::
                (r, t)
    {
        h := new binRelOnST<R,T>(
            f.dom(),  
            g.codom(), 
            set r, s, t | 
                r in f.dom() &&
                s in f.codom() &&
                (r, s) in f.rel() &&
                s in g.dom() && 
                t in g.codom() &&
                (s, t) in g.rel() ::
                (r, t));
    }
}