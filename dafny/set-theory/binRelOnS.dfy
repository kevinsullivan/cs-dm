include "binRelOnST.dfy"

module binRelS
{    
    import opened binRelST
    /*
    Abstraction of a polymorphic finite binary 
    relation over a set, S, of elements of type,
    T. 
    
    The concrete representatation of a value of
    this type is just an object of the binRelOnST
    class, where both of its type parameters are
    T, and where the domain and codomain sets are
    just S. This class specializes (restricts) 
    the more general binRelOnST class. Most of 
    the operations of this class just "delegate"
    to the underlying relation object. 
    */ 
    class binRelOnS<T(!new,==)>
    {
        /*
        Concrete representation: a binary relation
        on T X T.
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
        This constructor instantiates a binary relation
        on S X T using type, T, for both type parameters,
        a single set for the both the domain and codomain
        sets, and a set of T-T pairs as the relation, with
        the constraint that values in the relation be from
        the domain/codomain set.
        */
        constructor(elts: set<T>, pairs: set<(T,T)>)
            /*
            The relation has to be over the given set.
            */
            requires forall x, y :: 
                (x, y) in pairs ==> x in elts && y in elts;
            
            /*
            Dafny can't see into *method* bodies, so 
            explain as part of the spec what this method '
            achieves. Dafny needs this information for 
            later verifications.
            */
            ensures r.d == elts && r.c == elts && r.r == pairs

            /*
            The constructor leaves the object in a valid 
            state. All other operations require that an 
            object be Valid as a
            */
            ensures Valid();
         {
            r := new binRelOnST(elts,elts,pairs);
        }

        /*
        Accessor (projection) function: return the domain 
        set.
        */
        function method dom(): set<T>

            /*
            Every operation (function, method) of this 
            class except for the constructor require that
            an object be in a valid state for the operation
            to be applied. Every method is also required to
            ensure that it leaves this object in a valid
            state, so ensures Valid() is also included 
            below and in every other method. The idea is
            that the constructor establises the property
            of being valid, and every method preserves it,
            so it is an *invariant* property of objecst of
            this type. Specifying and ensuring preservation
            of state invariants of objects is essential,
            and the failure to do so properly is a major
            source of bugs in code.
            */
            requires Valid();
 
            /*
            Dafny needs to know what values a function reads
            in order to know what values its results might
            depend on, for purposes of later verifications.
            The "reads this" specification element informs
            the verifier that this function might read any 
            of the fields of this object.
            */
            reads this;

            /*
            This specification element, "reads r" tells Dafny
            that his function can call functions that in turn
            read fields of r.
            */
            reads r;

            /*
            As explained above, this (and every) operation is
            requires to leave this object in a valid state.
            */
            ensures Valid();
        {
            /*
            After all that, we just "delegate" this operation
            to the corresponding operation of the underlying
            binRelOnST object, by calling r.dom(). That this
            operation leaves the object in a valid state thus
            relies on r.dom() doing so. And that is the case,
            because Dafny verifies that function as doing so.
            */
            r.dom()
        }

        /*
        Accessor (projection) function: return the codomain 
        set. The detailed explanations for the preceding 
        function apply more or less directly to this and
        other operations in this class. We do not repeat
        the comments in every class.
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
        Accessor/projection function: return the 
        relation (pair set).
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
        Return true if and only if the relation is 
        single-valued (i.e., actually a function)
        */
        predicate method isFunction()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            /* Again, we just "delegate" this.isFunction()
            to r (the underlying binRelOnST object, by calling
            r.isFunction().
            */
            r.isFunction()  
        }

        
        /*
        Return true iff this relation is a function, 
        and it is an injective function, in particular.
        
        The properties of being injective, surjective, 
        or bijective apply to single-valued relations,
        i.e., to functions. We thus restrict the next
        three operations to apply only when this object
        satisfies is a function, which is to say that it
        satisfies the isFunction() predicate. We thus
        add this.isFunction() as a pre-condition to each
        of these operations. (We leave off the "this.", 
        as it's implicitly there already.) We then just
        delegate legal calls to these operations to the
        corresponding operations on r.
        */
        predicate method isInjective()
            reads this;
            reads r;
            requires Valid();
            requires isFunction();  // newprecondition
            ensures Valid();
        {
            r.isInjective()
        }
        
        
        /*
        Return true iff the relation is a function and 
        it is a surjective function, in particular. 
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
        Return true iff the relation is a function 
        and is bijective, in particular. 
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
        Return true iff the relation is total 
        (i.e., defined on every element of its
        domain set).
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
        Return true iff the relation is partial 
        (not total relative to its domain set).
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
        Return true iff this relation is reflexive.
        To be reflexive a relation must map every
        element of its domain to itself. 

        This funciton provides a good simple example
        of a unversally quantified predicate in Dafny.
        It can be read as "forall x (implicitly of type
        T), if x is in the domain of this relation then
        (x,x) is in the relation." The following few
        functions are written in the same style. What
        you have in these cases, then, is simply the
        mathematical definitions of these fundamental
        properties of relations expressed using Dafny 
        syntax.
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
        A relation is said to be a preorder if it is
        reflexive and transitive. That is, every element
        is related to itself, and if e1 is related to e2
        and e2 to e3, then e1 is also related to e3. The
        reachability relation for a direct graph is a
        preorder: every element reaches itself and if
        there's a path from a to b then a reaches b. 
        Given any relation you can obtain a preorder
        by taking its reflexive and transitive closure.
        Unlike a partial order, a preorder in general is
        not antisymmetric (viewing the relation as a 
        graph, there can be cycles in the graph). 
        Unlike an equivalence relation, a preorder is 
        not necesarily symmetric.
        */
        predicate method isPreorder()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            isReflexive() && isTransitive() 
        }

        predicate method isTotalPreorder()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
            {
                isPreorder() && isTotal()
            }


        /*
        Quasiorder is another name for a preorder.
        */
        predicate method isQuasiOrder()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            isPreorder()
        }

 
        /*
        A binary relation is said to be antisymmetric
        if whenever both (x, y) and (y, x) are in the
        relation, it must be that x == y. A canonical
        example of an antisymmetric relation is <= on
        the natural numbers. If x <= y and y <= x (and
        that is possible) then it must be that x == y.
        */
        predicate method isAntisymmetric()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();

        {
            forall x, y ::     x in dom()   &&   y in dom() &&
                           (x,y) in rel() && (y,x) in rel() ==> 
                           x == y
            // could also have written xRy ==> !yRx
        }


        predicate method isPartialOrder()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();

        {
            isReflexive() && isTransitive() && isAntisymmetric()
        }

        predicate method isTotalOrder()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();

        {
            isAntisymmetric() && isTransitive() && isTotal()
        }

 
        /*
        A relation on a set S is said to be irreflexive
        if no element is related, or maps, to itself.
        */
        predicate method isIrreflexive()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();

        {
            forall x :: x in dom() ==> (x,x) !in rel()
        }


        /*
        A binary relation on a set, S, is said to be 
        quasi-reflexive if every element that is related
        to some other element is also related to itself.
        */
        predicate method isQuasiReflexive()
             reads this;
            reads r;
            requires Valid();
            ensures Valid();

        {
            forall x, y :: 
                x in dom() && y in dom() && (x,y) in rel() ==> 
                    (x,x) in rel() && (y,y) in rel()
        }


        /*
        Returns the identity relation on the domain
        of this relation. Used, among other things, to
        compute reflexive closures.
        */
        method identityOnS() returns (id: binRelOnS<T>)
            requires Valid();
            ensures id.Valid();
            ensures id.dom() == dom() &&
                    id.rel() == set x | x in dom() :: (x,x);
            ensures Valid();
        {
             id := new binRelOnS(dom(), set x | x in dom() :: (x,x));
        }


        /*
        Return the union of this relation and the given 
        relation, t: b, basicaly (this + t), viewed as sets
        of pairs. The domain/codomain sets of this and t 
        must be the same.
        */
        method binRelOnSUnion(t: binRelOnS<T>) returns (r: binRelOnS<T>)
            requires Valid();
            requires t.Valid();
            requires t.dom() == dom();
            ensures r.Valid();
            ensures r.dom() == dom();
            ensures r.rel() == t.rel() + rel();
        {
            r := new binRelOnS(dom(),t.rel() + rel());
        }


        /*
        Return the intersection between this relation and 
        the given relation, t: b, basicaly (this * t). The
        domain/codomain sets of this and t must be the same.
        */
        method binRelOnSIntersection(t: binRelOnS<T>) 
            returns (r: binRelOnS<T>)
            requires Valid();
            requires t.Valid();
            requires t.dom() == dom();
            ensures r.Valid();
            ensures r.dom() == dom();
            ensures r.rel() == t.rel() * rel();
        {
            r := new binRelOnS(dom(),t.rel() * rel());
        }


        /*
        Return the difference between this relation and 
        the given relation, t: b, basicaly (this - t). The
        domain/codomain sets of this and t must be the same.
        */
        method binRelOnSDifference(t: binRelOnS<T>) 
            returns (r: binRelOnS<T>)
            requires Valid();
            requires t.Valid();
            requires t.dom() == dom();
            ensures r.Valid();
            ensures r.dom() == dom();
            ensures r.rel() == rel() - t.rel();
        {
            r := new binRelOnS(dom(), rel() - t.rel());
        }


        /*
        The reflexive closure is the smallest relation
        that contains this relation and is reflexive. In
        particular, it's the union of this relation and
        the identity relation on the same set. That is
        how we compute it here.
        */
        method reflexiveClosure() returns (r: binRelOnS<T>)
            requires Valid();
            ensures r.Valid();
            ensures r.dom() == dom();
            ensures r.rel() == rel() + set x | x in dom() :: (x,x);
            ensures Valid();
        {
            var id := this.identityOnS();
            r := binRelOnSUnion(id);
        }
 

        /*
        The reflexive reduction of a relation is the relation
        minus the idenitity relation on the same set. It is, to
        be formal about it, the smallest relation with the same
        reflexive closure as this (the given) relation.
        */
        method reflexiveReduction() returns (r: binRelOnS<T>)
            requires Valid();
            ensures r.Valid();
            ensures r.dom() == dom();
            ensures r.rel() == rel() -  set x | x in dom() :: (x,x);
            ensures Valid();
        {
            var id := this.identityOnS();
            r := binRelOnSDifference(id);
        }

        // transitive closure
        // transitive reduction



        /*
        A relation R on a set, S, is said to be well-founded
        if every non-empty subset, X, of S has a "minimum"
        element, such that there is no other element, x, in
        X, such that (x, min) is in X.

        As an example, the the less than relation over the
        infinite set of natural numbers is well founded 
        because in any subset of the natural numbers there 
        is because there is always a minimal element, m: an
        element that is less than every other element in the
        set. 
        
        The concept of being
        well founded turns out to be vitally important for
        reasoning about when recursive definitions are valid.
        In a nutshell, each recursive call has to be moving
        "down" a finite chain to a minimum element. Another
        way to explain being well-founded is that a relation
        is not well founded if there's a way either to "go 
        down" or to "go around in circles" forever. Here we
        give a version of well foundedness only for finite 
        relations (there can never be an infinite descending
        chain); so what this predicate basically rules out 
        are cycles in a relation.
        */
        predicate method isWellFounded()
            reads this;
            reads r;
            requires Valid();
            ensures Valid();
        {
            forall X | X <= dom() ::
                X != {} ==>
                    exists min :: min in X && 
                        forall s :: s in X ==> (s, min) !in rel()
        }

        /*
        The image of a domain value under a relation
        is the set of values to which the relation
        maps that domain element. This method provides
        this behavior. It computes and returns the 
        image of a domain element under this relation.
        It requires that the given value actually be
        in the domain set. Note that if the relation
        is not defined for an element in its domain,
        the image of that value will simply be the
        empty set.
        */
        function method image(k: T): (r: set<T>)
            reads this;
            reads r;
            requires Valid(); 
            requires k in dom();
            ensures Valid();
        {
            r.image(k)
        }


        /*
        The image of a *set* of domain elements is just
        the set of values that the relation maps those
        elements to. It basically "looks up" each domain
        element and returns the union of all the images
        of those values. A precondition for calling this
        function is that all argument values (in ks) be
        in the domain of this relation.
        */
        function method imageOfSet(ks: set<T>): (r: set<T>)
            reads this;
            reads r;
            requires Valid(); 
            requires forall k :: k in ks ==> k in dom();  
            ensures Valid();
        {
            r.imageOfSet(ks)
        }


        /*
        Given an element in the range of a relation, its
        preimage is the set of elements in in the domain
        that map to it. This function returns the preimage
        of a given value in the range of this relation. It
        is a precondition that v be in the codomain of this
        relation.
        */
        function method preimage(v: T): (r: set<T>)
            reads this;
            reads r;
            requires Valid(); 
            requires v in codom();
            ensures Valid();
        {
            r.preimage(v)
        }


        /*
        Compute image of a domain element under this relation.
        */
        function method preimageOfSet(vs: set<T>): (r: set<T>)
            reads this;
            reads r;
            requires Valid(); 
            requires forall v :: v in vs ==> v in codom();
            ensures Valid();
        {
            r.preimageOfSet(vs)
        }


        /*
        A relation is said to be defined for a given
        domain element, k, if the relation maps k to 
        at least one value in the codomain. 
        */
        predicate method isDefinedFor(k: T)
            reads this;
            reads r;
            requires Valid();
            requires k in dom();
            ensures Valid();
        {
            r.isDefinedFor(k)
        }

        /*
        If this relation is a function, then we can
        "apply" it to a single value, on which this
        function is defined, to get a single result. 
        */
        method apply(k: T) returns (ret: T)
            requires Valid(); 
            requires k in dom();   // only ask about domain values
            requires isFunction(); // only ask if this is a function
            requires isTotal();   // that is defined for every value
            requires isDefinedFor(k);  // and that is non-empty
//            ensures ret in image(k);  // want |image(k)| == 1, too
            ensures Valid();
        {
            ret := r.fimage(k);
        }

        method convertToBinRelOnST() returns (c: binRelOnST<T,T>)
            requires Valid();
            ensures c.Valid();
            ensures c.dom() == dom() && 
                    c.codom() == codom() && 
                    c.rel() == rel();
        {
            c := new binRelOnST(dom(), codom(), rel());
        }


        /*
        Return the relation g composed with this 
        relation, (g o this). The domains/codomains
        of g and this must be the same.
        */
        method composeS(g: binRelOnS<T>) 
            returns (h : binRelOnST<T,T>)
            requires Valid();
            requires g.Valid();
            ensures h.Valid();
            ensures h.dom() == dom();
            ensures h.codom() == g.codom();
            ensures h.rel() == set r, s, t | 
                    r in dom() &&
                    s in codom() &&
                    (r, s) in rel() &&
                    s in g.dom() && 
                    t in g.codom() &&
                    (s, t) in g.rel() ::
                    (r, t)
        {
            var f' := convertToBinRelOnST();
            var g' := g.convertToBinRelOnST();
            h := composeRST(g',f');
        }
    }
}