/-
In Lean and related proof assistants, such
as Coq, you can obtain proofs not only by
applying inference rules, such as eq.refl,
directly, but also by using programs, called
tactics, that automate some of the details
of finding and applying inference rules or
sequences of such rules.

As an example, we look at the "rfl" tactic,
which slightly simplifies the application of
the eq.refl inference rule. Let's first look
at a few uses of rfl.
-/

theorem t1 : 2 = 1 + 1 := rfl
theorem t2 : tt = tt := rfl

/-
The rfl tactics appear to be producing
proofs of the given propositions, and that
is indeed the case. If we #check t1 we'll
see that this is so. t1 is a proof of 0=0
and in fact is exactly eq.refl 0.
-/

#check t1
#reduce t1

/-
What rfl is doing is grabbing the left side
of an equality proposition, such as 2 or tt
in the examples here, and returning eq.refl
applied to that value.
-/

/-
EXERCISE: Use rfl to produce a proof, h, of
the proposition, "Hello" = "He" ++ "llo".

EXERCISE: Use rfl to prove p: 3*3+4*4=5*5.
-/

/- * A brief aside about terminology *-/

/-
Note: The word "theorem" in mathematics is generally
used to mean an "important" proposition that has been
proved. The word lemma is used to mean a less 
important proposition that has been proved, often as
part of a larger proof of a more important theorem.
Mathematicians also use the word corollary to refer
to a proposition the proof of which follows from the
proof of a more important theorem. You can read all
about the various words used to refer to things that
have been proved, or that are intended to be proved,
here: https://academia.stackexchange.com/questions/113819/is-it-acceptable-for-a-referee-to-suggest-changing-theorem-into-proposition.
For our purposes, we'll typically just use theorem.
-/

/-
As you have now seen, Lean's notion of equality
does not mean exact equality of expressions. It
means instead the equality the values to which 
they "reduce" when you "evaluate" them. We can 
prove 2 = 1 + 1 using rfl (or eq.refl of course) 
because the "literal expression", 2, reduces to 
the value 2; the function application expression, 
1 + 1 (wherein the plus function is applied to 
the two arguments, 1 and 1) also reduces to 2;
those two values are the same; and so eq.refl 2
generates a proof that type-checks. 
-/

/- 
EXERCISE: Prove as a theorem, tthof (a silly and 
uninformative name to be sure), that 2 + 3 = 1 + 4.

EXERCISE: Prove as a theorem, hpleqhl, that "Hello " 
++ "Lean! is equal to "Hello Lean!" (these values 
are of type string in Lean and the ++ operator here 
refers to the string concatenation function in Lean.)
-/

