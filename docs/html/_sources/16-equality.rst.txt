********************
Proofs of Equalities
********************

An expression, v1=v2, is a proposition that asserts the equality of
the terms v1 and v2.  The terms are considered equal if and only if
one can produce a proof of v1=v2. There is an inference rule defined
in Lean that can produce such a proof whenever v1 and v2 are exactly
the same terms, such as in 0=0.  This rule can also produce a proof
whenever v1 and v2 reduce (evaluate) to identical terms. So we can
also produce a proof of 0+0=0, for example, because 0+0 reduces to 0,
and then you have identical terms on each side of the =. This notion
of equality is called "definitional equality". As you'd expect, it's a
binary, reflexive, symmetric, and transitive relation on terms. It is
also polymorphic, and so can be used for any two terms of the same
type, A, no matter what A is. The Lean inference rule that produces
proofs of definitional equality is just rfl.

Here (following) are several terms that are definitionally equal even
though they're not identical. rfl is happy to build proofs for
them. The second example illustrates that terms that look pretty
different can still be definitionally equal. On the left we have a
nat/string pair. The .1 after the pair is the operator that extracts
the first element of the pair, here term 1-1. This term then reduces
to 0. The terms on either side of the = thus reduce to the same term,
0, which allows rfl to complete its work and return a value that is
accepted as being of the right type, i.e., as a proof of equality.

    theorem t0 : 1 - 1 = 5 - 5 := rfl
    theorem t1 : (1-1, "fidge").1 = 0 := rfl

What you are seeing here is a strategy of proving propositions that
assert equalities in two steps: first simplify (evaluate) the
expressions on either side of the =, and then certify a proof of
equality if and only if the resulting terms are identical.  Whether
you are using a proof assistant tool such as Lean or just doing
paper-and-pencil mathematics, this is a fundamental strategy for
proving propositions of a certain kind, namely propositions that
assert equalities.


Proofs Based on Properties of Equality
--------------------------------------

There are analogous strategies for dealing with other situations
involving equalities.  For example, if we have proofs of a = b and b =
c and we need a proof of a = c, then we would use an inference rule
that depends not on the reflexive property of equality but on that
fact that it is transitive: if a = b and b = c then a = c. Similarly,
there is a rule that reflects the symmetric property of equality:
given a proof of a = b, it builds and returns a proof of b = a. We do
not get into the details at this time.

By The Reflexive Property of Equality
+++++++++++++++++++++++++++++++++++++

    theorem byRefl: ∀ α : Type, ∀ a : α, a = a
            := λ (α: Type) (a: α), eq.refl a

An English-language proof of p = p would read, "... p = p is true by
the reflexive property of equality."  Remember: "rfl" is just a
shorthand for "eq.refl a", where "a" is the value on the left of the
equals sign.


By the Symmetric Property of Equality
+++++++++++++++++++++++++++++++++++++


    theorem bySymm: ∀ α : Type, ∀ p q: α, p = q → q = p 
        /-
        eq.symm applied to a proof of
        p=q constructs a proof of q=p
        -/
        := λ (α: Type) (p q: α) (pfpq: p = q), 
            eq.symm pfpq

    #check 1 = 2



By the Transitive Property of Equality
++++++++++++++++++++++++++++++++++++++

The transitive property of equality
provides a corresponding inference
rule, p=q, q=r ⊢ p=r. In Lean this 
rule is called eq.trans. We give an
example its use in proving a theorem
that simply asserts that equality 
has the transitiveity property.

    theorem byTrans: 
        ∀ α: Type, 
            ∀ p q r: α, 
                p = q → q = r → p = r :=
        λ α p q r pfpq pfqr, eq.trans pfpq pfqr


In ordinary English we'd say "if p=q and q=r then p=r. We could write
the theorem using and; we'd just have to access the proofs within the
pair constituting the proof of the conjunction."


    theorem byTrans': 
        ∀ α: Type, 
            ∀ p q r: α, 
                p = q ∧ q = r → p = r 
        /-
        Applying eq.trans to a proof of p=q and
        a proof of p=q and a proof of q=r yields
        a proof of p=r. Here we have to extract
        the proofs of p=q and q=r from the proof
        of (p=q ∧ q=r).
        -/
        :=  λ α p q r conj, 
            eq.trans 
                (and.elim_left conj)
                (and.elim_right conj) 


Optional: Substitutability of Equals
++++++++++++++++++++++++++++++++++++


    theorem substutabilityOfEquals: 
        ∀ α: Type, ∀ P: α → Prop, ∀ a1 a2: α,   
            a1 = a2 → P a1 → P a2 :=
            /-
            If a1 equals a2, then if the predicate
            (a proposition with a parameter), P, is
            true of a1, then P is also true of a2.
            -/
                λ α P a1 a2 eql, eq.subst eql


    /- An exercise: Example of an Exam Question -/
    theorem eq_quiz: ∀ (α : Type) (p q r s: α),
        p = q → (p = q → r = s) → q = r → p = s :=
            λ α p q r s pfpq pfpqrs pfqr, 
                eq.trans
                    (eq.trans
                        pfpq
                        pfqr)
                    (pfpqrs pfpq) 

    #check eq_quiz


