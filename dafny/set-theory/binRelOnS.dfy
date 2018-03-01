module binRelS
{    
    /*
    Abstraction of a finite binary relation on a 
    set, S. Underlying representation is a pair: 
    the domain set, S, and a set of pairs over S.
    */ 
    class binRelOnS<T(!new,==)>
    {
        var d: set<T>;
        var p: set<(T,T)>;
        predicate Valid()
            reads this;
        {
            forall x, y :: (x, y) in p ==> x in d && y in d
        }

        /*
        Constructor requires that all values appearing in 
        any of the pairs in p be in d. That is, the pairs
        in p must represent a relation on domain, d. Note
        that the "ensures d == dom && p == pairs" really is
        needed here: the bodies of methods are not visible
        globally within the class, so a visible postcondition
        describing what the constructor does is needed to
        enable verification that tasks need this knowledge.
        */
        constructor(dom: set<T>, pairs: set<(T,T)>)
            requires forall x, y :: 
                (x, y) in pairs ==> x in dom && y in dom;
            ensures d == dom && p == pairs;
            ensures Valid();
        {
            d := dom;
            p := pairs;
        }

        /*
        Return domain/range set
        */
        function method dom(): set<T>
            reads this;
            requires Valid();
            ensures Valid();
        {
            d
        }

        /*
        Return set of ordered pairs
        */
        function method rel(): set<(T,T)>
            reads this
            requires Valid();
            ensures Valid();
        {
            p
        }


        /*
        Return true iff the relation is single-valued (a function)
        */
        predicate method isFunction()
            reads this;
            requires Valid();
            ensures Valid();
        {
        forall x, y, z :: x in dom() && y in dom() && z in dom() &&
                            (x, y) in rel() && 
                            (x, z) in rel() ==> 
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
        forall x, y, z :: x in dom() && y in dom() && z in dom() &&
                            (x, z) in rel() && 
                            (y, z) in rel() ==> 
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
            (set x, y | x in dom() && y in dom() && (x, y) in rel() :: y) == dom()    
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
            ensures isTotal() ==> 
                    (forall x :: x in dom() ==> 
                        (exists y :: y in dom() && (x,y) in rel()))
            ensures Valid();
        {
            (set x, y | x in dom() && y in dom() && (x, y) in rel() :: x) == dom()
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
        Return true iff the relation is reflexive
        */
        predicate method isReflexive()
            reads this;
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
            requires Valid();
            ensures Valid();
        {
            forall x, y, z ::  x in dom() && y in dom() && z in dom() &&
                            (x, y) in rel() && 
                            (y, z) in rel() ==> 
                            (x, z) in rel() 
        }


        /*
        Exercise: formalize and implement a test for being
        an equivalence relation.
        */
    }
}