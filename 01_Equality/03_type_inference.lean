/- Type Inference -/

/-
Now as we've seen, given a value, t, of some type, 
T, Lean can tell us what T is. The #check command
tells us the type of any value or expression. The
key observation is that if you give Lean a value,
Lean can determine its type. 
-/

#check 0

/-
We can use the ability of Lean to determine the
types of given values to make it easier to apply
the eq.refl rule. If we give a value, t, as an
argument, Lean can automatically figure out its
type, T, which we means we shouldn't have to say
explicitly what T is.

EXERCISE: If t = 0, what is T? If t = tt, what is
T? If t = "Hello Lean!" what is T?

Lean supports what we call type inference to 
relieve us of having to give values for type
parameters explicitly when they can be inferred
from from the context. The context in this case
is the value of t.

We will thus rewrite the eq.refl inference rule
to indicate that we mean for the value of the T
parameter to be inferred. We'll do this by putting
braces around this argument.  Here's the rule as 
we defined it up until now.

T: Type, t : T
-------------- (eq.refl)
  pf: t = t

Here's the rewritten rule.

{ T: Type }, t : T
------------------ (eq.refl)
    pf: t = t

The new version, with curly braces around 
{ T : Type }, means exactly the same thing,
but the curly braces indicates that when 
we write expressions where eq.refl is 
applied to arguments, we can leave out the 
explicit argument, T, and let Lean infer it
from the value for t.

What this slightly modified rule provides is 
the ability to expressions in which eq.refl is 
applied to just one argument, namely a value, 
t. Rather than writing "eq.refl nat 0", for 
example, we'd write "eq.refl 0". A value for 
T is still required, but it is inferred from 
the context (that t = 0 so T is of type nat), 
and thus does not need to be given explicitly.
-/

/-
In Lean, the eq.refl rule is defined in just
this way. It's even called eq.refl. It takes 
one value, t, infers T from it, and returns a 
proof that that t equals itself! 

Read the output  of the following check command 
very carefully. It says that (eq.refl 0) is a
a proof of, 0 = 0! When  eq.refl is applied to 
the value 0, a proof of 0 = 0 is produced.
-/

#check (eq.refl 0)

/-
EXERCISE: Use #check to confirm similar conclusions
for the cases where t = tt and t = "Hello Lean!".

EXERCISE: In the case where t = tt, what value does
Lean infer for the parameter, T?
-/
