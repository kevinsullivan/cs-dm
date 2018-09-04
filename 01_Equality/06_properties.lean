/-

HOMEWORK: Read, complete, submit.

We've seen that equality is reflexive.
That is, everything is equal to itself.

It is also symmetric in the sense that
if any value, a, is equal to some other
value, b, i.e., if a = b, then b is also
equal to a, i.e., b = a. 

What this means is we have an inference 
rule that both expresses the symmetric
property of equality and allows us to 
compute a proof of b = a from any proof 
of a = b, no matter what a and b are (no 
matter what type, T, a and b have, and 
no matter what values they have of this
type).
-/

/-
  (T: Type) (a b: T) (ab: a = b)
  ------------------------------ (eq.symm)
           ba: b = a

-/

-- Let's see it in action in four lines
def a := 1
def b := 2 - 1
lemma ab : a = b := rfl 
#check ab           -- a proof of a = b
#check (eq.symm ab) -- a proof of b = a!

/-
This is a big success. We understand not
only the property of being symmetric but
that we can use symmetry to derive new
proofs from proofs that we already have.
In fact, eq.symm is a program that does
just this derivation, as we see here!
-/

/-
Finally we come to the notion that
equality is also transitive. That means 
that for any values, a, b, and c, if 
a = b, and if b = c, then it must be 
that consequently a = c as well. 

  {T : Type}, 
  { a b c: T },
  ab: a = b, 
  bc: b = c
  ------------ (eq.trans)
   ac: a = c

That is, if given proofs of a = b and 
b = c, eq.symm constructs and returns 
a proof of a = c. 

Let's see it in action. We've already
got variables a and b to work with. We
need one more, c.
-/

def c := 1

/-
We've also already got a proof of a = b.
It's easy to generate one of b = c. 
-/

lemma bc : b = c := rfl

/- 
And now we can apply eq.trans to these
two premise-proofs and it will construct
and return a proof of the conclusion. The
expression that applies eq.trans to these
two proofs is (eq.trans ab bc). Now for
the fun part!
-/

#check eq.trans ab bc


/-
EXERCISE: First write a textual inference
rule, let's call it eq_snart. It says that
if T is any type; if a, b, and c are values
of this type, T; and you are given proofs 
of a = b and c = b then you can derive a
proof of a = c. 
-/

/-
EXERCISE: Now "prove" that this rule is
valid by implementing it as a program 
that, when given any argument values of 
the specified types, returns a proof of 
the specified type (of the conclusion). 

Hint: Use eq.trans to construct the proof
of a = c. It's first argument will be ab, 
the proof that a = b. It's second argument
has to be a proof of b = c for it to work
to derive a proof of a = c; but all we've
got is a proof of c = b (in the reverse
order). How can we pass a second argument 
of type b = c to eq.trans, so that it can 
do its job, when we have at hand is a proof 
of c = b. Now a major hint: we already
have a way to construct a proof of b = c
from a proof of c = b. Just use it. 

Ignore the error message in the following 
incomplete code. The problem is simply that
the definition is incomplete, due to the
underscore placeholder. Replace the underscore 
with your answer. Leave parenthesis around 
your expression so that it gets evaluted
as its own term. 
-/

def eq_snart    { T : Type} 
                { a b c: T }
                (ab: a = b)
                (cb: c = b) :=
    eq.trans 
        ab 
        (_)

/-
EXERCISE: Use lean to implement a new rule 
that that, from a proof of c = b and a proof 
of b = a, derives (constructs and returns) a
proof of a = c. Call the proof eq_snart' 
(why not, it sounds funny).
-/

/- * Conclusion * -/

/-
You now begin to see the power of proof
assitants. We can now compute with proofs
and the type checker makes sure that we
can (for all intents and purposes) never
use a proof that is not a valid proof of
the proposition that it claims to prove.
This represents a discontinuous leap over
the the state of mathematical practice, 
where proofs are beautiful little essays
rather than values we can compute with.
-/

/-
EXERCISE: Here we use eq_snart rather 
than eq.trans direcly to prove a = c, 
given proofs of a = b and c = b.
-/

lemma cb : c = b := rfl
#check cb
theorem aeqc : a = c := eq_snart _ _

/-
In general, there are many ways to prove 
a given theorem. Each distinct proof is 
nevertheless an inhabitant of the tyep of
the proposition that it proves, and each
suffices as evidence to justify a truth
judgment for the proposition. In many
cases, the particular proof object that 
is used
-/ 

/-
SUMMARY: In this section (1) you first
recalled  that the equality relation is 
reflexive, symmetric, and transitive. 
(2) You saw that in Lean, these are not 
just abstract ideas; there are also  
inference rules that you can apply to 
to arguments of the right types to 
build proofs of new propositions. (3) 
You also saw that you can prove your own
inference rules by writing programs that
implement them! Such programs can use
already accepted inference rules (such
as eq.refl, eq.symm, eq.trans) in their
implementations. Thereafter, the new 
rules are as good as the old, and can 
then also be used to construct proofs 
that might be needed.
-/


