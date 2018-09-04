/-
Now here we're going to pull a little trick. 
It's based on the idea that a "proof", whatever
that is (!), serves as "evidence" that justifies
a truth judgment about a proposition. So we are
now technically distinguishing between a proof
of a proposition and the truth judgment that it
justifies. Nevertheless, we will assume that a
truth judgment for some proposition, P, is in
fact justified if and only if we have a proof
of P.

To denote the fact that we have a proof, p, 
of some proposition, P, we will write p : P. 
Now, the key idea is that having a proof is
the evidence we need to judge that P is true.
Moreover, if we've judged P to be true, then
we must have a proof, p, of P.

In other words, P is true if and only if we 
have evidence (a proof), p, for P. We can 
write this statement in the language of logic
like this: "p : P →  P : true".  We'd read 
this as saying "if p is a proof of P then P
is true." 

The evidence, i.e., proof, p, for P, justifies  
the judgement, P : true. Moreover, the only
way to justify such a judgement is with such 
a piece of evidence, i.e., with a proof. In 
the logic of Lean, proof is truth and truth
requires a proof. 
-/

/-
Given that having a proof of P means that one
can conclude the truth of P, we can write an 
equivalent inference rule like this (compare 
with the previous):

p : P, q : Q
------------ (and.intro)
 r : P ∧ Q
 
This then says, "If you give me a proof, p, of
some proposition, P, and if you also given me a
proof, q, of some proposition Q, then I promise
to give you back a proof, r, of the proposition,
P ∧ Q." 

As a shorthand, mathematicians and logicians
would usually elide the ": true" and the "p :" 
bits, so you'd usually see this rule written
informally like this:

   P, Q
   ----- and.intro
   P ∧ Q

However, if we want to be really precise, we'd
write the rule like this:

  { P Q : Prop } (p : P) (q : Q)
  ------------------------------ (and.intro)
         pf : P ∧ Q

This is the final form, as we'll see in more
detail in material to come. It says that if 
P and Q are propositions, and if p is a proof
of P and q is a proof of Q, then applying the
and.intro rule to p and q returns a proof of
P ∧ Q. We thus now have a rule to establish
the truth of a proposition of P ∧ Q by using 
this inference rule to construct a proof of
the proposition P ∧ Q from given proofs of 
its constituent propositions. 

As we'll see in a bit, the expression,
(and.intro p q), which you can read as simply
applying the function, and.intro. to the proof
"values", p and q, returns (reduces to) a value
that is a proof of P ∧ Q. That's where we are
headed.
-/

/- 
EXERCISE: What is returned when the and-introduction
inference rule, viewed as a program, is applied to two
proofs: one of the proposition, 0 = 0, and one of the
proposition, "Hello" = "Hello"?

EXERCISE: Why could this rule never be applied (in
any reasonable logic) to produce a proof (thus a
truth judgement) for the proposition, 0 = 0 ∧ 0 = 1?
-/