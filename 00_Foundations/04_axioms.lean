/- *** Axioms *** -/

/-
In a mathematical or logical system, some propositions 
are taken to be true unconditionally: without the need 
for any prior "input" proofs.

An inference rule that requires no proof inputs, 
and that nevertheless lets you judge some proposition 
to be true, is called an axiom. We also use the term, 
axiom, to refer to the proposition that is the 
conclusion of the rule, and that is thereby judged 
true unconditionally. 

An axiom viewed as an inference rule with no
proofs/judgements as inputs would be written
with no proof/judgment premises/arguments above
the line.

For example, if we were to take the proposition, 
0 = 0, as an axiom, we could write it like this: 

           <---- note the absence of premises
-----
0 = 0

What this says then is that without having proved 
or judged any other propositions to be true you can
nevertheless assume that 0 = 0 is true. Equivalently,
without providing any proofs of other propositions
as arguments, this rule will still hand you back a
proof of 0 = 0, thereby justifying the judgment that
0 = 0 is true. In this case, you could say that the
logic includes 0 = 0 as an axiom.
-/

/-
It would not be convenient, however, to include
a separate axiom in a logic for every individual
natural number. We'd end up with an infinity of
such axioms, and that would be problematical for
the definition of the semantics of the logic. 
What we would like is to have a single inference
rule that covers an infinity of special cases.
Indeed, we'd like to have a rule that defines
that everything is equal to itself, not matter
what value, or what type of value it is. 
-/

/- ** An inference rule for equality in general ** -/

/-
Intuitively you would suppose that the proposition,
0 = 0, should be true in any reasonable logical system. 

There are two ways a logic could make this happen. 
The first is that the logic could provide 0 = 0 as 
an axiom, as we just discussed. 

That'd be ok, but then we'd need similar axioms for 
every other number. We'd also need similar axioms
for every object of every other type: person, car, 
plant, atom, book, idea, etc. We end up with a pretty
unweildy (and infinite) set of axioms. Moreover, if
we were ever to define a new type of objects (e.g.,
digital pets), we'd have to extend the logic with 
similar inference rules for every value of the new
type. (Fido = Fido, Spot = Spot, Kitty = Kitty, etc).

What would be much better would be to have just one
inference rule that basically allow us to conclude
that *any* object, or value, of any type whatsoever 
is always equal to itself (and that nothing else
is ever equal to that object).

It'd go something like this: if T is any "type" 
(such as natural number, car, person), and t is any 
object or value of that type, T (e.g., 0 is a value
of type "natural number", or "nat"), then you can 
unconditionally conclude that t = t is true.  

We could write this inference rule something like
this:

  T: Type, t : T
  -------------- (eq_refl)
     pf: t = t

In English, "if you're given that T is a (any) 
type and t is a value of that type, then the
eq_reflexive inference rule derives a proof of 
t = t. In informal English, you could say, 'for
any t (of any type_, t = t by the reflexive
property of equality". So there: *that* is the
fundamental reason why 0 = 0. It's an essential
property of the equality relation (on any type).

(Detail: This notion of equality is called Leibniz
equality.)

EXERCISE: Why exactly can this rule never be used 
to derive a proof of the proposition that 0 = 1?
-/

/- * Type judgments * -/

/-
Above the line in this inference rule, we meet a 
new kind of judgment here: a type judgment. If X 
is some type, and x is a value of that type, X, 
we can denote this fact by writing x : X. We read 
this as "x is of type X."
-/

/- * The types of types * -/

/-
The Lean tool that you're using here is based on a
foundational theory called type theory. In type
theory, every object (or value) has a single type.
Every parameter, such as an argument to a function.
has a type. Every expression has a type. 

In Lean you can check the type of an expression
by using the #check command. Note that ℕ is math
shorthand for the type of natural numbers, i.e.,
non-negative integers (thus zero on up). Hover
your mouse over the #check commands to see what
are the types of 0, "Hi!", and tt in Lean.
-/

#check 0
#check "Hi!"
#check tt

/-
Here's the key idea: types are values, too! It
thus follows that a type must have a type. So 
what is the type of a type? 

Answer: If T is a type, then it's type is called 
"Type".
-/

/-
EXERCISE: Use the #check command the see what is 
the type of nat, bool, and string.
-/

/-
So, if T is some type, then we'd write the type 
judgment, "T : Type". And if T is a type, and t 
a value of type, T, then we'd also write t : T. 
-/

/-
With all that out of the way, we can once again 
write and now more fully understand the inference 
rule for equality that we really want. 

T: Type, t : T
-------------- (eq-reflexive)
  pf: t = t

Those are now type judgments above the line. You can 
understand this inference rule as saying this: "if you 
give me a T that is a type (e.g., bool, nat, string), 
and if you also give me a value, t, of type, T, (e.g.,
0 or true), then I will give you back a proof that 
t = t. This single inference rule thus defines a very 
sensible notion of equality for all values of all types 
that exist or might ever be defined. 

So now, rather than a separate axiom for 0 = 0,
another one for 1 = 1, another for true = true, and
yet another for Fido = Fido, so forth, we now have 
a single inference rule that gives them all just as
special cases. We are given this inference rule as 
something close to an axiom, in the sense that the
only "proofs" it requires requires as inputs are
proofs that T is a type and t is a value of that
type. Where do these proofs come from? They come
from the Lean type checker!

Now as we've seen, give a value, t, of some type, 
T, Lean can tell us what T is. The #check command
tells us the type of any value or expression. This
is helpful because it means that in principle, we
could re-write the inference rule as follows, where
the curly braces around { T : Type } means that we
don't have to give a value of T explicitly when we
apply the eq-reflexivity inference rule, because
T can be inferred from t.

  { T: Type }, t: T
  ----------------- (eq-refl)
      pf: t = t

In Lean, the eq-reflexivity rule is formalized 
in this way and is called eq.refl. It takes one 
value, t, infers T from it, and returns a proof 
that that t equals itself!
-/

#check eq.refl 0 -- rfl
#check eq.refl "Hello Lean!"
#check eq.refl tt
#check eq.refl bool    -- even types are values
#check eq.refl (0 = 0) -- including propositions!

