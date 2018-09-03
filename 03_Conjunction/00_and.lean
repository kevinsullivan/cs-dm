/-
Intuitively, if a proposition P is true and a
second proposition Q is true, then the more
complex proposition, "P and Q" is also true.
This proposition is written symbolically as
P ∧ Q. In mathematical logic, we say that 
the proposition, P ∧ Q, is the conjunction 
of the individual propositions, P and Q. 

To give us some propositions and proofs to
use in examples, let's define P and Q to be 
simple equality propositions, and p and q 
to be proofs of these propositions.
-/

def P : Prop := 0 = 0
def Q : Prop := 1 = 1

theorem p : P := eq.refl 0
theorem q : Q := eq.refl 1

/-
We note that rfl doesn't work here. It's 
the right idea, but the proposition, P, 
to be proved isn't written as an equality,
so rfl doesn't know what to do with it. 
We just just eq.refl directly instead.
-/

/- * SYNTAX OF CONJUNCTIONS * -/

/--/
Now the syntax of proposition logic allows
us to form a new proposition, P ∧ Q.
-/

def P_and_Q : Prop := P ∧ Q

#check P_and_Q -- it's a proposition
#check P ∧ Q   -- same thing

/- * SEMANTICS OF CONJUNCTIONS * -/

/- * INTRODUCTION RULE * -/

/-
Now intuitively, P ∧ Q should be true if
and only if P is true and Q is true, which
in the logic of Lean is to say if we have 
a proof of P and a proof of Q. The and.intro
inference rule formalizes this idea. It says
if you give me propositions, P and Q, and 
proofs, p and q of P and Q respectively, 
then I will give you back a proof of P ∧ Q.

  { P, Q : Prop } (p: P) (q: Q)
  ----------------------------- and.intro
            pf : P ∧ Q


The and.intro takes two explcit arguments: a proof 
of P and a proof of Q. It infers P and Q from p 
and q. It then derives a proof of P ∧ Q. 

Here is an example of its use in Lean
-/

theorem pf: P ∧ Q := 
    and.intro p q -- study this carefully!

/-
Ok, let's decode that. We're proposing a theorem.
The proposition we aim to prove is P ∧ Q, which is
really just 0 = 0 ∧ 1 = 1. To produce a proof of
this proposition, we need a proof of 0 = 0. That
is p. We also need a proof of 1 = 1. That is q.
If we then apply the rule to p and q we can expect
to get back a proof of P ∧ Q, and the Lean checker
confirms that indeed we do.

You might be getting the sense that these
inference rules are sort of like functions:
They take propositions, proofs, and other
values as arguments and they compute and
return proofs as results. This is exactly
what is happening here. What you're seeing
is how programs like Lean turns propositions
and proofs into objects that can be handled
and transformed by programs! It's like your
ordinary discrete math class on steroids.
-/

/- * PROOF TREES * -/

/-
A key point is that what we just did is to
build a larger proof, pf, from two smaller
ones, p and q. Those proofs in turn we built
using the eq.refl inference rule applied to
the values 0 and 1, respectively. We can now
visualize the whole construction as what we
call a proof tree, or derivation (with more
than one level of rules being applied).

eq.refl 0    eq.refl 1
---------    ---------
  0 = 0        1 = 1
---------------------- 
     0 = 0 ∧ 1 = 1

We can read such a proof tree either from
the top to the bottom or from the bottom to
the top. We can also translate such a tree
into English. Most mathematicians would just
provide the English language proof, leaving
it to human and social processes to check
that it's good. We now have the benefit of
automated proof checking. 

Reading it from the top we might say the
following. By the reflexive property of
equality, we derive that 0 = 0 and that 
1 = 1. These lemmas both now been proved
separately, a proof of their conjunction 
follows immediately.
QED

Now as one seeking to prove P ∧ Q (the
conclusion), one would work from bottom
to top. The reasoning would go like this:
To prove the conclusion, we need proofs
of ach conjunct. We obtain a proof of the
first, 0 = 0, by noting that this follows
from the reflexive property of equality.
So does a proof of 1 = 1. Now having 
proved the individual conjuncts, the truth 
of the conjunction follows immediately.
QED.

You can see that the everyday working
matheatician elides many details, such
as the precise principle used to derive
the truth of the conjunction. The lack
of detail in informal proofs makes them
at best nearly impossible for machines 
to check. Reading and checking them
really relies on human mathematical
understanding.

Nevertheless, whether you are asked to
write an informal proof or a formal one,
the process of deriving a proof often 
involves this kind of "backwards chaining." 

When asked to prove a proposition, X, we 
generally try to find other propositions, 
such as S and T, such that if we had 
proofs of S and T, we could then apply 
a valid reasoning step (inference rule) 
to derive a proof of X. 

One thus reduces the problem of proving 
X to the sub-problems of proving S and T. 
One  then backward-chains this way until 
one finally reaches ... axioms, i.e., 
rules with no proofs required above the 
line. Axioms are the "base cases" in 
the recursive decomposition of the 
overall problem: there is no need
to recurse any further once you've 
reach the bottom!

To be really precise about it, there
is one more layer in the proof tree:
it's where the Lean type checker gives
us proofs that 0 and 1 are of type nat;
and that's what eq.refl needs as its
input. The type checker in turn gives
us proofs of these type judgments by
means of yet further, but not hidden,
logic reasoning.

 0: nat       1 : nat
---------    ---------
eq.refl 0    eq.refl 1
---------    ---------
  0 = 0        1 = 1
---------------------- 
     0 = 0 ∧ 1 = 1

QED!

Now you're looking at a depiction
of a mathematically precise proof.
The English just presents such an
object in a more natural language,
but at the cost of a massive loss
of precision and checkability.  The
downside of the formal proof object
is that it's not in the form of a
story; and as you can imagine, in
cases where proofs get massssive,
understanding why they are the way
they are can be near impossible.
But that's why we have machines.

In practice, you should really
know how to produce both formal
and informal proofs. Better yet,
you might someday try some tools
that produce formal proofs for 
you. (Such a tool is Dafny. We
will perhaps see it later.)
-/

/-
EXERCISE: What "smaller" propositions 
might you want to prove to prove that
5 = 1 + 4 ∧ "Strike" = "S" ++ "trike". 
Prove those smaller propositions giving
them whatever names you choose. Then 
write the theorem in Lean that proves 
the final result using and.intro.
-/

/- * AND ELIMINATION * -/

/- 
Given a proof of P ∧ Q, it's clear that
P should be true individually, and Q too.

The and elimination rules provide us with
these reasoning principles, allowing us to
derive P from P ∧ Q, and Q from P ∧ Q. We
call them and.elim_left and and.elim_right.


{ P Q: Prop } (paq : P ∧ Q)
--------------------------- and.elim_left
         pfP : P


{ P Q: Prop } (paq : P ∧ Q)
--------------------------- and.elim_left
         pfQ : Q
-/

#check and.elim_left pf
#check and.elim_right pf

/-
EXERCISE: Fill in the "sorry" words in 
the following incomplete theorems with 
proofs obtained by applying the and 
elimination rules to our proof, pf, of
P ∧ Q. (Note: Sorry says, "please just
accept the theorem as proved, i.e., as
an axiom.It's dangerous to use sorry 
except as a temporary placeholder for
a proof that you promise to come back
and fill in later.")
-/

theorem pfP : P := sorry
theorem pfQ : Q := sorry

/- * COMMUTATIVITY OF CONJUCNTION *-/

/-
Now we've really got some power tools. We
can prove equalities. From constituent proofs
we we prove conjunctions and from proofs of
conjunctions we can obtain consituent proofs.
With these tools new can now start to state
and prove interesting properties of logical
operators, here conjunction.

Let's first state a claim informally. If
P ∧ Q is true then Q ∧ P also must be true
as well.

We have a proof of P ∧ Q (0 = 0 ∧ 1 = 1)
already. Can we construct a proof of Q ∧ P?

First, let's formaliez the proposition.
-/

def Q_and_P : Prop := Q ∧ P

/-
How can we generate a proof of Q_and_P?
Well, given the tools we have at hand,
we have no option other than to apply
the and introduction rule to a proof of
Q and a proof of P (in the reverse order).
And given a proof of P ∧ Q, we can get 
our hands on those individual proofs by 
using the and elimination rules. We'd
then just use them as arguments in the
other order to and.intro. Voila!
-/

theorem pfQaP : Q ∧ P :=
  and.intro 
    (and.elim_right pf) 
    (and.elim_left pf)

/-
The general inference rule, which we
will call and.comm, short for "and
commutes", says that if P and Q are 
*any* propositions, and we have a 
proof, paq, of P ∧ Q, then we can
obtain a proof, qap, of Q ∧ P. We
could write the rule like this (with
the arguments P and Q again being 
implicit, insofar as they can be
inferred from paq).

{ P Q: Prop }, paq : P ∧ Q
-------------------------- and.comm
        qap: Q ∧ P

We can now even see how we might
implement this rule ourselves --
literally as a program! We'll call
it "and_commutes".
-/

def and_commutes { P Q: Prop } (paq: P ∧ Q) :=
  and.intro (and.elim_right paq) (and.elim_left paq)

/-
In this program we use the same curly
brace notation as introduced informally
above to indicate parameters that are to
be inferred from context. That is, we can
apply this function to a proof of P ∧ Q,
without expliciting giving P and Q as
parameters, to obtain a proof of Q ∧ P.
Does it work?
-/

theorem qap : Q ∧ P := and_commutes pf

/-
Holy cow, it does! We applied our new
*general purpose proof converter* to 
a particular proof, here for 0 = 0 ∧
1 = 1, to obtain a proof of 1 = 1 ∧ 
0 = 0. But we can see that this will
work no matter what P and Q are. 


We have thus proven that conjunction 
is commutative not just for the special 
case of 0 = 0 ∧ 1 = 1, but in general.
And we did this by writing a program 
that converts a proof of P ∧ Q, for 
*any* propositions P and Q, into a 
proof of Q ∧ P.

Now things are getting interesting.
-/

/-
EXERCISE: From a proof of 1 = 1 ∧ tt = tt,
use my_and_comm to prove tt = tt ∧ 1 = 1.
-/

/-
Having now proved that and commutes, as
matheaticians would say, we can now use
this principle as a valid principle in
all future reasoning. Indeed in the work
of everyday mathematics one had proved 
P ∧ Q and need a proof of Q ∧ P, it'd 
be a simple matter of saying "Q ∧ P 
follows from the communitativity of 
conjunction." Many mathematicians would
just say, "Q ∧ P follows immediately,"
leaving it to the reader to know that
the commutativity property of ∧ is the
real justification for the conclusion.
-/
