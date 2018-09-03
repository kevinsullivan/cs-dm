/-
So far, all of the propositions that we've
seen are in the form of assertions about
equalities: 0 = 0, 1 = 1, 2 + 3 = 4, and so
on. And we've seen how to prove propositions
of this kind (that are actually true) using
eq.refl and rfl as a shorthand.

We are now about to set out to explore the
different forms of propositions that arise
in predicate logic. 

In this unit, we meet the simplest of all
propositions, even simpler than equality
statements, namely the propositions that
in lean are called "true"  and "false".
First, true is the proposition that is 
always trivially provable. 
-/

/- The "true introduction" inference rule -/

/-
Here's the inference rule for true. Note 
that it doesn't require an inputs/premises 
at all. It is truly an axiom. Makes sense:
You can alway assume that the proposition
true is true. 

  -------- (true.intro)
  pf: true

The true.intro inference rule is called
true.intro because it is an introduction
rule in the sense that it introduces a 
true in the conclusion that wasn't in the
premises (of which there are none here).

Here then is a formal (mathematically 
precise) and mechanically checked proof
of the proposition, true, in Lean.
-/

theorem t : true := true.intro

#check t
#reduce t

/- 
That's it! Super easy. 
-/

/-
There is no introduction rule for false!
-/

/-
Whereas true is trivially provable, the
proposition, false, has not proof and can
never be proved. Viewed as a type, it has
no values at all. It's what we call an
uninhabited type. Therefore there can be
no inference rule or sequence of rules 
that derive a proof of false, because
such a thing simply does not exist! That
is after all the meaning of false: it is
not true, so there must be no proof of
it, otherwise it would be true, and 
that would be a fatal contradiction.
-/


/-
The difference between tt/ff and the
propositions, true and false.
-/


/-
To clarify one major potential point of
confusion it's imperative to see that the
propositions, true and false, are not the 
same as the boolean truth values, which
in Lean are called tt and ff. In some 
other languages, they're called "true" 
and "false", which really is a source of
possible confusion.
-/

/-
First, let's confirm that the types of
tt and ff are bool.
-/

#check tt
#check ff

/-
You will recall that we can assign 
these values to variables of type bool
-/

def boolean_false := ff

#check boolean_false
#reduce boolean_false


/-
By contrast, we cannot assign the
value tt as a proof of true. It's not
even of the right type. Uncomment the
following line to see that this is the
case. Read the error message carefully.

EXERCISE: Read and explain the error
message to a colleague in your class.
-/

-- theorem bad : true := tt


/- * EX FALSO QUOD LIBET * -/

/-
Now we come to a very fundamental
concept in logic: from a contradiction,
you can derive a proof of any proposition
whatsoever. To put it in English terms,
if the impossible has happened, then 
anything goes! 

The inference rule for this says that 
if you're given a proof of false, let's 
call it f, and any proposition, P, 
whatsoever (any value, P, of type 
Prop!), then you can derive a proof 
of P, and the false disappears from
the conclusion (which is why we call
this inference rule false elimination).

Here's the rule:

  f : false, { P : Prop }
  ----------------------- false.elim
        pf : P

Note that the proposition argument, 
P, is not to be given explicitly as
an argument to false.elim, but is to
be inferred from context, instead. 
-/

/-
Let's see how this works in Lean.
Let's start by simply asserting as 
an axiom, without proof, that f is 
a proof of false. 
-/

axiom f : false

/-
Well, it was probably a bad idea.
It just says, "trust me and accept
that the impossible just occurred."
The problem is that our logic is 
now inconsistent and anything at
all can be proved. We just feed
our proof of false to false.elim
to prove any proposition at all.
Let's try to prove 0 = 1.
-/

theorem zeqo : 0 = 1 := false.elim f

/-
It will very occasionally be useful
to add an axiom to Lean, but one must
take extraordinary care to ensure that
it is consistent with the underlying
logic of lean. The axiom that there
is a proof of false immediately makes
the whole logic useful because it
collapses the distinction between
true and false entirely, and in this
case, any claim can be proven true,
and that would put us logically in
a post-truth work, which would be a
bad and useless place to be.
-/

/-
EXERCISE: Prove true = false (given
that we've assume there is a proof of
false).
-/

/-
As a final observation, we note that
there are some propositions that one
might think of as being false, and thus
provable from a contradiction, but that
we cannot even state in Lean. For
example, we can't even state the claim
that 1 = tt because Lean requires that
the types of the arguments on each side
of the = be the same.


EXERCISE: Try it. The error message that
appears is a little bit complicate but in
a nutshell it's saying "I can't find a way
to coerce/convert 1 into a bool, and so I
can't do anything with this expression."
In simple terms, the expression 1 = tt 
has a type error. It's not even a well
formed expression.
-/



