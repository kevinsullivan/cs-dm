/*
(c) Kevin Sullivan. 2018.
*/

module binRelST
{    
    /*
    Abstraction of a finite binary relation on a 
    set, S. Underlying representation is a triple: 
    the domain set, S, the co-domain set, T, and 
    a set of pairs over S X T.
    */ 
    class binRelOnST<Stype(!new,==),Ttype(!new,==)>
    {
        var d: set<Stype>;      // domain: set of values of type S
        var c: set<Ttype>       // codomain: set of values of type T
        var r: set<(Stype,Ttype)>;  // relation: set of pairs from s X t
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
        constructor(dom: set<Stype>, codom: set<Ttype>, rel: set<(Stype,Ttype)>)

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
        function method dom(): set<Stype>
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
        function method codom(): set<Ttype>
            reads this;
            requires Valid();
            ensures Valid();
        {
            c
        }


        /*
        Accessor: Get the underlying set. Note that dom() 
        and codom() also return the same results.
        */
        function method S(): set<Stype> 
            reads this;
            requires Valid();
            ensures Valid();
        {
            dom()
        }


       /*
        Accessor: Get the underlying set. Note that dom() 
        and codom() also return the same results.
        */
        function method T(): set<Ttype> 
            reads this;
            requires Valid();
            ensures Valid();
        {
            codom()
        }


        /*
        Return set of ordered pairs
        */
        function method rel(): set<(Stype,Ttype)>
            reads this
            requires Valid();
            ensures Valid();
        {
            r
        }


        /***********************************/
        /* ARE GIVEN NODES RELATED OR NOT? */
        /***********************************/

        predicate method related(x: Stype, y: Ttype)
            reads this;
            requires Valid();
            requires x in S() && y in T();
            ensures Valid();
        {
            (x, y) in rel()
        }


        predicate method unrelated(x: Stype, y: Ttype)
            reads this;
            requires Valid();
            requires x in S() && y in T();
            ensures Valid();
        {
            (x, y) !in rel()
        }


        /*******************************/
        /* FUNCTION-RELATED PROPERTIES */
        /*******************************/

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
        Return true iff the relation is an injective function
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
        Return true iff the relation is a surjective function  
        */
        predicate method isSurjective()
            reads this;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            /*
            A function, r, is surjective iff for every y in the codomain, there is some x in the domain such that the pair (x, y) is in r.
            */ 
            forall y :: y in codom() ==> 
                exists x :: x in dom() && (x,y) in rel()
        }


        /*
        Return true iff the relation a bijective function
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
        Return true iff the relation is total function
        */
        predicate method isTotal()
            reads this;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            /*
            A function is total if for every x in the 
            domain, there is some y in the codomain with 
            (x,y) in r
            */
            forall x :: x in dom() ==> 
                exists y :: y in codom() && (x,y) in rel()
        }

        
        /*
        Return true iff the relation is partial (relative to its domain set)
        */
        predicate method isPartial()
            reads this;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            !isTotal()
        }


        /*
        Return true iff value, x, of type Stype, is in domain
        */

        predicate method inDomain(x: Stype)
            requires Valid();
            reads this;
            ensures Valid();
        {
            x in dom()
        }


         /*
        Return true iff value, y: Ttype, is in codomain
        */

        predicate method inCodomain(y: Ttype)
            requires Valid();
            reads this;
            ensures Valid();
        {
            y in codom()
        }


        /*
        Return true iff this relation is defined 
        for the given value. In some mathematical 
        writing, the term "domain" is often used 
        to refer to the set of values on which 
        a relation is defined. Our usage of the 
        term differs.
        */
        predicate method isDefinedFor(x: Stype)
            requires Valid()
            requires inDomain(x);
            reads this;
        {
            exists y :: y in codom() && (x, y) in rel()
        }


        /*
        Return true iff given value is in range of
        relation: not just in codomain set but mapped
        to by some value for which relation is defined.
        */
        predicate method inRange(y: Ttype)
            requires Valid()
            requires inCodomain(y);
            reads this;
        {
            exists x :: x in dom() && (x, y) in rel()
        }


        /*
        Compute image set of a single value under this relation.
        */
        function method image(x: Stype): set<Ttype>
            reads this;
            requires Valid(); 
            requires inDomain(x);
            ensures Valid();
        {
            set y | y in codom() && (x, y) in r
        }


        /*
        Compute preimage set of a value under this relation
        */
        function method preimage(y: Ttype): set<Stype>
            reads this;
            requires Valid(); 
            requires inCodomain(y);
            ensures Valid();
        {
            set x | x in dom() && (x, y) in rel()
        }


        /*
        Compute image set of a set of values under this relation
        */
        function method imageOfSet(xs: set<Stype>): set<Ttype>
            reads this;
            requires Valid(); 
            requires forall x :: x in xs ==> inDomain(x)
            ensures Valid();
        {
            /*
            For each x in the given set of x values (xs) find all
            the (x, y) pairs; return the set of all such y values
            */
            set x, y | x in xs && y in codom() && (x, y) in r :: y
        }


        /*
        Compute preimage set of a set of values under this relation.
        */
        function method preimageOfSet(ys: set<Ttype>): set<Stype>
            reads this;
            requires Valid(); 
            requires forall y :: y in ys ==> inCodomain(y);
            ensures Valid();
        {
            set x, y |  y in ys && x in dom() && (x, y) in r :: x 
        }


        /*
        Compute image of a domain element under this relation.
        This code assumes there is exactly one element in the 
        set from which the value is drawn (but this assumption
        is not yet verified).
        */
        method fimage(x: Stype) returns (y: Ttype)
            requires Valid(); 
            requires isFunction();  // ensures single-valuedness
            requires inDomain(x);   // ensures function is non-empty
            requires isDefinedFor(x);
            ensures Valid();
            ensures y in set y' | y' in codom() && (x, y') in r
        {
            /* 
            Assign to y the one value in the image of x. This
            code depends on the fact that there is exactly one
            element in the image set, because the relation is
            both defined for x and is single-valued (a function).
            However, we haven't verified this assumption.
            */
            y :| y in image(x);
        }


        /*
        Helper function: given a set of pairs, return the set
        of inverted (reversed) pairs.
        */
        static function method invert<S(==),T(==)>(ps: set<(S,T)>): 
            set<(T,S)>
        {
            set x, y, p | p in ps && x == p.0 && y == p.1 :: (y, x)
        }


        /*
        Construct and return the inverse of this relation.
        */
        method inverse() returns (r: binRelOnST<Ttype,Stype>)
            requires Valid();
            ensures r.Valid();
            ensures r.dom() == codom();
            ensures r.codom() == dom();
            ensures r.rel() == invert(rel());
        {
            r := new binRelOnST(codom(), dom(), invert(rel()));
        }


        /*
        Helper function: "join" two sets of pairs, g and f,
        returning (g o f), on a common element in the codomain
        of f and the domain of g. Defining this function once
        here eliminates redundancy in the definition of the 
        compose function, below. 
        
        Along with the two sets of pairs, g and f, this function  takes sets representing the domains and codomains from which the values in the pairs are drawn: the domain of f, shared codomain of f and domain of g, and the codomain of g. 
        */
        static function method join<X(!new), Y(!new), Z(!new)>
            (g: set<(Y,Z)>, f: set<(X,Y)>, 
             fdom: set<X>, shared: set<Y>, gcodom: set<Z>): 
            set<(X,Z)>
        {
            set x, z | 
                x in fdom && z in gcodom &&
                exists y :: y in shared && 
                (x, y) in f && (y, z) in g :: (x,z)
            /*
            set x, y, z | 
                x in fdom && y in shared && z in gcodom &&
                (x, y) in f && (y, z) in g :: (x, z)
            */
        }


        /*
        Returns h, the composition of "this" relation, from S to T, with the relation, that, from T to R, yielding a relation from 
        S to R. S-values to R-values. Composition of relations is a 
        special case of composition of functions. More details to be
        discussed in class.
        */
        method compose<Rtype>(g: binRelOnST<Ttype,Rtype>) 
            returns (h : binRelOnST<Stype,Rtype>)
            requires Valid();
            requires g.Valid();
            requires g.dom() == codom();
            ensures h.Valid();
            ensures h.dom() == dom();
            ensures h.codom() == g.codom();
            ensures h.rel() == join(g.rel(), rel(), dom(), g.dom(), g.codom())
            ensures forall x, z :: 
                (x, z) in h.rel() ==> x in dom() && z in g.codom();
        {
            h := new binRelOnST<Stype, Rtype>(
                    dom(),  
                    g.codom(), 
                    join(g.rel(), rel(), dom(), g.dom(), g.codom())
                );
        }
    }
}