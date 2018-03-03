include "binRelOnST.dfy"

module binRelS
{    
    import opened binRelST
    /*
    Abstraction of a finite binary relation on a 
    set, S. Underlying representation is a pair: 
    the domain set, S, and a set of pairs over S.
    */ 
    class binRelOnS<T(!new,==)>
    {
        /*
        We represent a binary relation, R, over a set,
        T, as a value of the type of binary relations
        over two types, but where both types are just S.
        */
        var r: binRelOnST<T,T>;

        /*
        This object is valid if it's a valid relation on
        S X T and the domain and codomain are the same set.
        */
        predicate Valid()
            reads this;
            reads r;
        {
            r.Valid() && r.dom() == r.codom()
        }


        /*
        Constructor just instantiates a binary relation
        on S X T with the type, T, of the single set over
        which the current relation is defined, setting the
        domain and codomain sets to be the same set, elts.
        */
        constructor(elts: set<T>, pairs: set<(T,T)>)
            requires forall x, y :: 
                (x, y) in pairs ==> x in elts && y in elts;
            ensures r.d == elts && 
                    r.c == elts && r.r == pairs
            ensures Valid();
         {
            r := new binRelOnST(elts,elts,pairs);
        }

        /*
        Return domain set
        */
        function method dom(): set<T>
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            r.dom()
        }

        /*
        Return codomain set
        */
        function method codom(): set<T>
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            r.codom()
        }

        /*
        Return set of ordered pairs
        */
        function method rel(): set<(T,T)>
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            r.rel()
        }


        /*
        Return true iff the relation is single-valued (a function)
        */
        predicate method isFunction()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            r.isFunction()  
        }

        
        /*
        Return true iff the relation is a function and is injective
        */
        predicate method isInjective()
            reads this;
            reads r;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            r.isInjective()
        }
        
        
        /*
        Return true iff the relation is a function and is surjective 
        */
        predicate method isSurjective()
            reads this;
            reads r;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            r.isSurjective()
        }

        /*
        Return true iff the relation a function and is bijective
        */

        predicate method isBijective()
            reads this;
            reads r;
            requires Valid();
            requires isFunction();
            ensures Valid();
        {
            r.isBijective()    
        }


       /*
        Return true iff the relation is total (relative to its domain)
        */
        predicate method isTotal()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            r.isTotal()
        }

        
        /*
        Return true iff the relation is partial (relative to its domain set)
        */
        predicate method isPartial()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            !r.isTotal()
        }


        /*
        Return true iff the relation is reflexive
        */
        predicate method isReflexive()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();        
        {
            forall x :: x in dom() ==> (x, x) in rel() 
        }


        /*
        Return true iff the relation is symmetric
        */
        predicate method isSymmetric()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            forall x, y ::  x in dom() && y in dom() &&
                            (x, y) in rel() ==> (y, x) in rel()
        }


        /*
        Return true iff the relation is transitive
        */
        predicate method isTransitive()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            forall x, y, z ::  
                x in dom() && y in dom() && z in dom() &&
                (x, y) in rel() && 
                (y, z) in rel() ==> 
                (x, z) in rel() 
        }


        /*
        Exercise: formalize and implement a test for being
        an equivalence relation.
        */
       predicate method isEquivalence()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            isReflexive() && isSymmetric() && isTransitive() 
        }


        /*
        Compute image of a domain element under this relation.
        */
        function method image(k: T): (r: set<T>)
            reads this;
            reads r;
            requires Valid(); 
            ensures Valid();
        {
            r.image(k)
        }



        /*
        Compute image of a domain element under this relation.
        */
        method imagef(k: T) returns (ret: T)
            requires Valid(); 
            requires isFunction();
            requires isTotal();   // ensures defined for every value
            requires k in dom();  // ensures function is non-empty
            ensures ret in image(k);
            ensures this == old(this);
            ensures r == old(r);
            ensures Valid();
        {
            ret := r.imagef(k);
        }
    }
}