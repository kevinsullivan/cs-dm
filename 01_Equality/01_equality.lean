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
unwieldy (and infinite) set of axioms. Moreover, if
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
object or value of that type, T (e.g., t could be 
the value, 0, which is a value of type "natural 
number", or "nat" for short), then you can derive
that t = t is true.  

We could write this inference rule something like
this:

  T: Type, t : T
  -------------- (eq_refl)
     pf: t = t

In English you could pronounce this rule as
saying, "if you can give any type, T, and any 
value, t, of that type, T, then the eq_refl 
rule will derive a proof of the proposition
that t = t. In mathematical logic, this notion 
of equality is called Leibniz equality.

EXERCISE: Give an expression in which eq_refl
is applied to two arguments to derive a proof
of 0 = 0.

EXERCISE: Why exactly can this rule never be used 
to derive a proof of the proposition that 0 = 1?
-/