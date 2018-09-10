/-
Intuitively, if a proposition P is true and a
second proposition Q is true, then the more
complex proposition, "P and Q" is also true.
This proposition is written symbolically as
P ∧ Q. In mathematical logic, we say that 
the proposition, P ∧ Q, is the conjunction 
of the individual propositions, P and Q. 

There's an inference rule for that. It says
that if P and Q are propositions (types of
type Prop), and if you have a proof of P and
you have a proof of Q then you can derive a
proof of P ∧ Q. Moreover, the form of that 
proof is basically the pair of proofs, (p, q). 

{P Q : Prop }, p : P, q : Q
--------------------------- (∧-intro)
        (p, q): P ∧ Q


To give us some propositions and proofs to
use in examples, let's define P and Q to be 
simple equality propositions, and let's then
define p and q to be proofs of P and Q.
-/

def P : Prop := 0 = 0
def Q := 1 = 1 -- type inference works here

theorem pfP : P := eq.refl 0
theorem pfQ : Q := eq.refl 1


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

/- * AND INTRODUCTION RULE * -/

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
          pf_PQ : P ∧ Q


The and.intro takes two explicit arguments: a 
proof of P and a proof of Q. It infers P and Q from pf_P and pf_Q. It then derives a proof of 
P ∧ Q. 

Here is an example of its use in Lean
-/

theorem pf_PQ: P ∧ Q := 
    and.intro pfP pfQ -- study this carefully!

/-
Ok, let's decode that. We're proposing a theorem.
The proposition we aim to prove is P ∧ Q, 
which is really just 0 = 0 ∧ 1 = 1. To produce
a proof of this proposition, we need a proof 
of 0 = 0. That is p. We also need a proof of 
1 = 1. That is q. If we then apply the rule to 
p and q we can expect to get back a proof of 
P ∧ Q,=. The Lean checker confirms that we do.

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
mathematician elides many details, such
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
cases where proofs get massive,
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

/- * Proving conjunctions with tactics * -/

/-
One can always prove a proposition by
giving an exact proof term, but these
terms are like programs, and they can
get large and complicated. Sometimes,
indeed often, it's easier to develop
them step by step.

A key idea is that we start with the
goal at the bottom of a proof tree, the
goal (proposition) to be proved, and by
working backwards through the tree, we
can identify the smaller propositions
for which we need proofs so as to be
able to apply a final rule to construct
the desired proof. 

Consider again the goal of proving the
conjunctive proposition P ∧ Q. If we have
a proof of P and a proof of Q then we 
can apply the and.intro rule to build
the proof we need. Well, that breaks the
overall goal into two subgoals, and we
can then solve them recursively (i.e., 
as sub-problems to solve nested within
the solution to the overall problem).

In particular, we can *split* the goal
of proving a conjunction into sub-goals,
one for each conjunct. We then solve 
the sub-problems and finally combine
the partial solutions into a final result 
using and.intro.

Whether you are using a tool like Lean
or are just writing informal mathematical
proofs, the use of decomposition of a
large problem into pieces, recursively
solving of the parts, and ultimately
the combination of the partial results
into a final result, is essential and
ubiquitous. Indeed, it's a general way
to solve complex problems in almost
any domain. The key is being able to
break a problem into parts that can 
be solved independently. 
-/

/-
In Lean, we can build proofs this way
using tactic scripts. First we apply 
the and.intro rule. Used in a script in 
this way, it works backwards! Rather 
than combining proofs for P and Q into 
a proof of P ∧ Q, it decomposes the 
top-level goal of proving P ∧ Q into
two sub-goals: to prove P and to prove
Q. The problem of proving P ∧ Q is 
thus decomposed into the problem of
proving premises needed to make the
and.intro rule succeed. We then use
additional tactics too solve each of
the sub-problems, one by one. 

Open the Messages view, then put your 
cursor at the beginning of each line in 
the following script and study how the 
tactic state changes as you go.
-/

theorem pf_PQ': P ∧ Q := 
begin
  apply and.intro,
  exact (eq.refl 0),
  exact (eq.refl 1),
end

/-
An English-language rendition of this
proof-constructing procedure would go
like this: "We split the problem of
proving P ∧ Q into the sub-problems,
of proving P and proving Q. This is
a valid step because the and.intro
rule tells us that having such proofs
will suffice to prove the main goal. 
A proof of P follows from the reflexive
property of equality, and a proof of Q
also then follows similarly. QED."

Constructing proofs in this way is
very much like writing programs by
first writing the Main routine, having
it call subroutines, and then writing
the subroutines. Here instead we start
with the main goal, P ∧ Q. We apply
an inference rule to break down the
problem of proving the goal into one
or more problems of proving sub-goals,
and once we're done with that, a proof
of the top-level goals follows by the
application of the mai inference rule.

We call this approach to development
of programs, and of proofs, top-down
decomposition. Sometimes a software
will say that she's using "top-down
structured programming" to design her
code. Learning to think this way is
a major step forward for a computer
scientist.
-/

/-
There's another way, of course, to
build a proof, or a program, and that
iss to write the sub-routines first and
then to integrate them into a larger
program by writing code that uses them. 
We call such an approach "bottom-up." 

You can similarly develop proofs using
a bottom-up approach. You first obtain the proofs of sub-goals that you'll need
and then you "integrate" (combine) them 
by applying some inference rule.

We now introduce a style of Lean proof 
scripts that supports such a bottom-up 
approach to constructing proofs. Here's 
an example where we prove the same proposition but in a bottom-up manner.
-/

theorem pf_PQ'': P ∧ Q := 
begin
  have X := (eq.refl 0),
  have Y := (eq.refl 1),
  apply and.intro X Y
end

/-
Study very carefully how the tactic state
changes as you advance through the script.
The first tactic we use is "have." It
gives a name to a proof for a sub-goal
that you will then use later on. Here, the 
name X is given to a proof of 0 = 0. Once 
this tactic has run, you will see the proof state update to a new state in which you 
have a proof X of 0 = 0 (before the ⊢),
with P ∧ Q as desired proposition to be
proved. Next we give a name to, and then
subsequently also have a proof of Q. And
finally, we apply the and.intro rule to
these two proofs, which are now available
in the "context" of the proof state (before
the ⊢) to build a proof of the overall goal. Lean checks and accepts that proof thereby
solving the overall problem. QED, as they
say. 

This style of proof scripts starts to 
look like proofs that a mathematician
might write. This one could be read 
like this: "We have a proof of P,  
(eq.refl 0). Let's call it X. We
also have a proof of Q, (eq.refl 1).
Let's call it Y. Given proofs X and Y
we now apply the and.intro rule to 
X and Y to derive the proof we need. 
QED."
-/

/-
Whether you write exact proof objects, 
or use top-down or bottom-up scripting 
methods, the key point to bear in mind
is that everything ultimately relies
on the inference rules. They are what
is most fundamental. Moving from the
conclusion to the premises of and.intro
is how we decompose the top-level goal,
P ∧ Q, into sub-goals. Moving from the
premises X and Y down through the
and.intro rule to a proof of P ∧ Q is
how we merge bottom-up partial results
into an overall solution. And of course
if we're going to write a proof object
exactly, the expression we need is one
in which eq.refl is used. It's thus very
important that you familiarize yourself
deeply with the introduction (and also 
the elimination) inference rules for
predicate logic. Now we move on to the
elimination rules for and (∧).
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
--------------------------- and.elim_right
         pfQ : Q
-/


-- recall that t is a proof of P ∧ Q
#check and.elim_left pf_PQ
#check and.elim_right pf_PQ

/-
EXERCISE: Fill in the "sorry" words in 
the following incomplete theorems with 
explicit proof objects obtained by applying 
the and elimination rules to our proof, pf_PQ,
of P ∧ Q. 

Note: Sorry says, "please just accept 
the theorem as proved: an axiom. It's 
dangerous to use sorry  except as a 
temporary placeholder for a proof that 
you plan fill in later."
-/

theorem pfP' : P := and.elim_left pf_PQ
theorem pfQ' : Q := sorry

/-
Here are two script-based proofs.
-/

theorem pfP'' : P :=
begin
  exact and.elim_left pf_PQ
end

theorem pfP''' : P :=
begin
  have pfP := and.elim_left pf_PQ,
  exact pfP
end

/- * COMMUTATIVITY OF CONJUNCTION *-/

/-
Now we've really got some power tools. We
can prove equalities. From constituent 
proofs we can prove conjunctions, and 
from proofs of conjunctions we can obtain
proofs of the individual conjuncts. With 
these tools in hand we can now start to 
state and prove essential mathematical 
properties of logical operators, here of
conjunction (and, ∧) .

Let's first state a claim informally. If
P ∧ Q is true then Q ∧ P must be true
as well. We won't prove the general case
here, but we will show that from a proof
of (0 = 0 ∧ 1 = 1) we can derive a proof
of (1 = 1 ∧ 0 = 0).

We already have the propositions, P := 
0 = 0, Q := 1 = 1, and a proof, t, of
P ∧ Q (i.e., of 0 = 0 ∧ 1 =1 ). Now
let's give a name to the proposition
that (1 = 1 ∧ 0 = 0).

-/

def Q_and_P : Prop := Q ∧ P -- reverse!

/-
How can we generate a proof of Q_and_P?
Let's think in a top-down manner. Start
with the goal, Q ∧ P, and ask how it can
be proved. The only way we can prove it 
at present is by applying and.intro to a
proof of Q and a proof of P (in this new 
and reversed order!).

So the form of a proof simply has to 
be (and.intro _ _), where the first _
is a proof of Q and the second _ is a
proof of P.

If all we start with is a proof, t, of 
P ∧ Q, how can get the proofs, pfP of 
P and pfQ of Q, that we need? Easy! Apply 
the and.elimination rules to t to get
first a proof of Q then a proof of P,
and then use those proofs as arguments 
to and.intro. 
-/

theorem pfQaP : Q ∧ P :=
  and.intro 
    (and.elim_right pf_PQ) 
    (and.elim_left pf_PQ)

/-
EXERCISE: Write a top-down proof script
to prove the same proposition, calling
the result pfQaP'.

EXERCISE: Write a bottom-up proof script
to prove the same proposition, calling 
the result pfQaP''.
-/
 
theorem pfQaP' : Q ∧ P :=
begin
  split,
  exact (and.elim_right pf_PQ),
  exact (and.elim_left pf_PQ),
end

theorem pfQaP'' : Q ∧ P :=
begin
  have pfQ := (and.elim_right pf_PQ),
  have pfP := (and.elim_left pf_PQ),
  apply and.intro pfQ pfP
end

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
-------------------------- and_commutes
        qap: Q ∧ P

We can now even see how we might
implement this rule ourselves --
literally as a program! We'll call
it "and_commutes".
-/

def and_commutes { P Q: Prop } (paq: P ∧ Q) :=
  and.intro 
    (and.elim_right paq) 
    (and.elim_left paq)

/-
In this program we use the same curly
brace notation as introduced informally
above to indicate parameters that are to
be inferred from context. That is, we can
apply this function to a proof of P ∧ Q,
without explicitly giving P and Q as
parameters, to obtain a proof of Q ∧ P.
Does it work?
-/

theorem qap : Q ∧ P := and_commutes pf_PQ

/-
Holy cow, it does! We applied our new
*proof converter* to convert a proof
of 0 = 0 ∧ 1 = 1 into a proof of 1 = 1 ∧ 
0 = 0. We might guess that this will
work no matter what P and Q are, and
indeed that is the case, because we
wrote our program to be general with
respect to what the propositions P and
Q are. We have thus in effect proven 
that conjunction is commutative: that
for any propositions, P and Q, if P
∧ Q is true, then so must be Q ∧ P.

Now things are getting interesting.
-/

/-
EXERCISE: From a proof of 1 = 1 ∧ tt = tt,
use and_commutes to prove tt = tt ∧ 1 = 1.
-/

/-
Having now proved that "and commutes," 
as mathematicians would say, we can now 
use this principle in all future reasoning.
Indeed in the work of everyday mathematics,
if one had proved P ∧ Q and needed a proof 
of Q ∧ P, it'd be a simple matter of saying 
"Q ∧ P follows from the commutativity of 
conjunction." Many mathematicians would
just say, "Q ∧ P follows immediately,"
leaving it to the reader to know that
the commutativity property of ∧ is the
real justification for the conclusion.
-/

