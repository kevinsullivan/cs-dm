/-
In this chapter we explore the formal definition of the algebra called
Boolean algebra. Boolean algebra is an algebra over a set of two values,
usually called true and false, with a set of operators, such as "and,"
"or," and "not." It was invented by George Boole (thus it name) to capture 
the forms of logical human thought in a mathematical (algebraic!) form. 

Boolean algebra should already be familiar to you--though maybe not as 
"an algebra"--rom your study of the syntax and evaluation of Boolean 
expressions in your CS1 class. But whereas you took Boolean algebra as
a built-in capability of the programming language you used in CS1, now
we will actually build that algebra from scratch.

In the process of doing this, we will encounter a number of concepts 
that are at the foundations of mathematics and mathematical logic. They
include the following:

- Boolean algebra as a case studing in defining algebras
  * the carrier set of Boolean values, { true, false }
  * the standard Boolean operations
- implementing the carrier sets of algebras using inductive type definitions
- implementing the operations of algebras as pure functional programs 
- asserting and proving properties of such an implementation
- propositions and proofs
  * by simplification and reflexivity of equality
  * by exhaustive case analysis

The overall contribution of this chapter is the definition (and a
working implementation) of the algebra of Boolean values comprising
an inductive definition of the set of Boolean values as a type, the
definition  of set of operators over this set in the form of pure
functional programs, and the statements and proofs of a few simple
expected properties of this algebra to provide some evidence that
we got it right.

Along the way, we will meet a few ancillary ideas that are needed
for our implementation. These concepts are not unique to Lean but
appear across a broad range of programming and verification languages 
and systems.

- namespaces (common to most programming systems)
- inductive type definitions (common across most functional languages)
- the #check command in Lean (common across many proof assistants)
- pure functional programming (a major category of programming languages)
- type inference
- function types
- pattern matching (common to many functional programming languages)
- propositions as types (common across constructive logic proof assistants)
-/
