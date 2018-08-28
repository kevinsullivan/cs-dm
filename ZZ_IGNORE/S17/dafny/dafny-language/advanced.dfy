/*
At present this file contains only a list of Dafny language
issues not covered in the material presented to date. We will
introduce many, though not all, of these topics as needed as
we go along.
*/

/* EXPRESSIONS

lambda expressions
object types
iterator types
numeric conversion
case
match
quantifier
set comprehension
map comprehension
*/

/* COMMANDS 

yield
patterns in update/assignment statements
"*"" guards
binding guards
loop specifications, invariants, termination, framing
match
assume
forall
modify
calc
skeleton
*/

/* TYPES -- OO

Objects (class instances), and traits (to be discussed) are of "reference" types, which is to say, values of these types are stored on the heap. Values of other types, including sets and sequences, are of "value types," which is to say values of these types are stored on the stack; and they're thus always treated as "local" variables. They are passed by value, not reference, when passed as arguments to functions and methods. Value types include the basic scalar types (bool, char, nat, int, real), built-in collection types (set, multiset, seq, string, map, imap), tuple, inductive, and co-inductive types (to be discussed). Reference type values are allocated dynamically on the heap, are passed  by reference, and therefore can be "side effected" (mofified) by methods to which they are passed. They include arrays and objects.
*/

/* OTHER

predicate
lemma
*/
 