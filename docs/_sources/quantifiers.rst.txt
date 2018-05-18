Quantification: First-Order Logic
=================================

We now address quantifiers with some care.  We've been seeing and
using them all along, of course. What we do in this chapter is to
address them more rigirously. We discuss elimination and induction
rules, and the fundamental concepts of induction principles and their
use to build proofs by induction We'll then address quantification in
practice: e.g., in Dafny and maybe SQL. Quantifiers also complicate
automated verification systems because they allow for the expression
of very complex specifications. We will briefly address ways in which
programmers can think about helping Dafny when it needs guidance about
where to look, e.g., for witnesses needed to prove existentials.

Universal and Existential Quantification
========================================

Introduction and Elimination Rules for Exists
=============================================

Introduction and Elimination Rules for Forall
=============================================

Induction Principles and Algebraic Data Types
=============================================

This takes us in particular to induction principles and proofs (where
we redeem our earlier aside on the injectivity of constructors). This
is how we introduce truth claims with *for alls* elements in a given
domain (or type), particularly in cases where the domain quanitified
over is infinite.

As an example, we'd like to be able to deduce (prove) that every
program written in some new language either type checks and is
accepted by the type checker, and in this case no runtime errors can
occur, or that it is expressly rejected by the checker, and that the
checker will never *get stuck*.

How might we every prove something about all programs in a language?

