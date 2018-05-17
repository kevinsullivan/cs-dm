********************
Proofs of Inequality
********************

How do you prove zero does not equal one? What principle actually make
this proposition true? The principle in play here is the *injectivity
of constructors of inductively defined types.* The *semantics* of an
inductive type definition are such that different constructors always
produce different values. The inductive data types for our simplified
Boolean expression language provided two constructors, for example:
*bTrue* and *bFalse*. It follows from the injectivity of constructors
that these two values cannot be equal. To see why zero does not equal
one, we need to understand how the natural numbers themselves can be
defined inductively, leading us to the notion of Peano Arithmetic. It
will then be clear, given the injectivity of constructors, that zero
cannot be equal to one, or to any other natural number.

Peano's Princples
=================

Why Zero Isn't One
==================

Proofs of Inequality in Lean
============================

More to come
============
