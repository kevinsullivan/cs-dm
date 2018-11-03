example : 
    ∀ (x : Type), 
    ∀ p :  x → Prop,
    ∀ q : x → Prop, 
    (∀ x, p x) ∨ (∀ x, q x) → 
    ∀ x, p x ∨ q x := 
/-
What does this proposition say, and
do you believe it at least might be
true? What it says is that if every
x has property p or every x has property 
q, then every has the property of having
property p or property q. It seems this
should be true. Consider the cases: if
every x has property p, then certainly
every x has the property of having
property p or having property q,
because every x has property p. In
the other case, where every x has
property q, every x still has the
property of having property p or q,
because every x has property q. So
let's now go ahead and prove it.
-/
begin
/- 
First, use ∀ introduction by introducing 
the universally quantified variables as 
assumptions: that x is an arbitrary type; 
and p and q are arbitrary properties of
values of this type. 
-/
intro x,
intros p q,
/-
To prove the remaining implication, start
by assuming the premise of the goal, then
proceed to prove the conclusion.
-/
assume pf : (∀ x, p x) ∨ (∀ x, q x),
/-
To prove this ∀, we once again use the
rule for ∀ introduction: assume that we
have an arbitrary value (of the right 
type), then show that the remaining  
predicate is true for that arbitrary 
value. That proves that it is true no 
matter what value we picked, and thus
for all values of that type. The value
here will become the witness for the 
final or introduction, so we'll call it
w.
-/
assume w,
/-
What we now need to prove is that w has
property, p, or that it has property, q.
What we now have to work with is a value,
is a proof that every x has property p or 
that every x has property q. From that we 
should be able to prove that w has either
property p or property q. To prove it we will use an elimination rule for ∀. If we have a proof, pf, of ∀ t : T, P t, and we have a value, v : T, then, treating pf as a function, we can apply pf to v to get a proof of P v.  Unfortunately, both of the ∀s are stuck inside the disjunction, pf. 
And we don't know which one is true, only that at least one of them is. To use them,we have to apply or elimination, which is tantamount to proof by case analysis on pf. 
-/
apply or.elim pf,
/-
Now we have to show that now matter which
of the two cases holds, the goal is true.
-/

-- Case, all x have property p

/-
When you use the cases tactic, it takes
care of introducing the assumptions of the proofs of the respective disjuncts. 
When you apply or.intro directly, you 
have to do it yourself. We do this for
each of the two cases that follow.
-/
intro all_x_px,
/-
Now we have w, a value of type x,
and a proof that every x has property
p. This is where we use ∀ elimination,
applying the proof that every value 
has a property to a specific property
to get a proof that that specific value
has the property. 
-/
have w_p := (all_x_px w),
/-
And now it's a simple matter of using
or an introduction rule to finish off
this case.
-/
exact or.inl w_p,

/-
We've now proven that if pf is true 
because every x has property p then
the goal is true. Now we show that 
the goal is also true if every x has
property q. The goal thus follows from
the truth of pf. The proof is symmetric
to the one we just gave/
-/ 
intro all_x_q,
have w_q := (all_x_q w),
exact or.inr w_q,
end


example: 
    ∀ (X : Type), 
    ∀ (p q : X → Prop), 
    (exists x, p x) ∧ (exists x, q x) → 
    exists x, (p x ∧ q x) 
/-
What this proposition asserts is that 
there is some object with property p
and there is some (possibly other) object with property q then there is some object
with the property of having both property
p and property q. To make this concrete,
it could be saying that if there's a ball
that is green and there is a ball that is
yellow, then there is a ball that is both
green and yellow. But that conclusion does
not follow logically from the premises!
This proposition is not true, and it's 
easy to come up with counter-examples.

Let's go ahead and see what happens if
we try to prove it, and how you can get
yourself into what looks like a state
where a proof is possible, even though
it's not.
-/    
    :=
begin
-- first, the usual ∀ introductions
intros,
/-
we'll need to do ∃ intro with a witness,
w, and a proof that w has both properties,
p and q.

What we have to work with is the proof,
a, a conjunction of two existentially
quantified propositions. We use and elim
to get at the constituent proofs, then we
will try exists elim to get witnesses to
each predicate, (p x) and (q x).
-/

have ex_x_p := a.left,
have ex_x_q := a.right,
apply exists.elim ex_x_p,
intro x, intro px,
apply exists.elim ex_x_q,
intro x, intro qx,

/-
It looks like we're almost done!
All we need is a proof of p x ∧ q x.
-/
have px_and_qx := and.intro px qx,

exact px_and_qx,

/-
Houston, we've had a problem!

invalid type ascription, term has type
  p x ∧ q x_1
but is expected to have type
  ∃ (x : X), p x ∧ q x
types contain aliased name(s): x
-/

-- Cannot finish proof.

/-
What went wrong? The problem is that
the two existentially quantified parts
of the original premise do correctly
promise that there some object with
property p and some object with property
q, but there's no promise that they are
the same object. For that, the premise
would have to be ∃ x, p x ∧ q x. Be
sure you understand that the scope of
the quantified variable, x, extends 
only to the end of the proposition!
Somewhat annoyingly, Lean let's you
use the same name when you introduce
these two objects into your context.
But note carefully: There really are 
two things named x, and there is no
way to conclude that they're the same
object! "Under the hood", Lean knows
they're not the same, and when you 
finally try to pass off what *looks*
like a proof of p x ∧ q x as such a 
proof, Lean actually tells you, hey,
what you've actually got here is a
proof of p x ∧ q x_1, where x_1 is
not necessarily the same as x.

A crucial lesson to learn from this
example is that you really have to
think about whether a proposition to
be proved actually makes logical sense.
In this case, it doesn't. The fact
that Lean let's you get to the end
of what looks like a valid proof 
before it reminds you that you are
using the same name, x, for objects
that are not the same, is annoying,
but now you will remember!

We will give full credit for getting
to this point in the proof, because
this one was tricky. 
-/
end



example: 
    ∀ (X : Type), 
    ∀ (p q : X → Prop), 
    (exists x, p x) ∨ (exists x, q x) → 
    exists x, p x ∨ q x :=
begin
/-
Here the proposition asserts that
if there's object with property p
or there's an object with property
q, then there's an object that has
the property of having either property
p or property q. That seems logically
sensible, so we will go ahead and try
to prove it.

We see that what we have to work with
is the assumption that either there's
and object with property p or one with
property q, and what we have to prove
is there's an object with one of these
properties. To construct the required
proof, we'll have to use ∃ introduction.
To get the "ingredients" we'll need to
do that, namely a witness and a proof,
we're going to have to use (1) or elim,
i.e., case analysis, on the disjunction,
and (2) ∃ elim in each case. We'll use
the cases tactic to do or elimination.
-/
intros,
cases a with ex_px ex_qx,
-- case ex_px
apply exists.elim ex_px, intros,
apply exists.intro a, 
exact or.inl a_1,
-- case ex_qx
apply exists.elim ex_qx, intros,
apply exists.intro a, 
exact or.inr a_1,
end