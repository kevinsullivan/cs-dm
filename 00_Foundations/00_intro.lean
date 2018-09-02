/-
*** MATHEMATICAL LOGIC ***

/- *** Overview *** -/

In this unit you will learned the following concepts, among others:

* mathematical logics as formal systems
* propositions, including their syntax and semantics
* truth judgments 
* inference rules, their meaning and notation
* axioms
* proofs as evidence that justify truth judgments
* propositions about equality
* automating propositions and proofs in Lean
* an axiom defining equality in general
* type judgments
* proof trees (derivations)
* set theory and type theory as axiomatic foundations for mathematics
-/

/- *** Formal systems *** -/

/-
Modern mathematics, and discrete mathematics in particular,
are formal (mathematical) logical systems. 

Logical systems in turn are rooted in the concepts of 
propositions, truth judgments, inference rules, and 
proofs, or derivations, as evidence supporting truth
judgments.

This is pretty abstract. Let's see what it really means.
-/

/- ** Propositions and truth judgments ** -/

/-
A proposition is a mathematically precise assertion that 
some state of affairs is true in some domain of interest.

For example, in the domain of basic arithmetic, the claim
that 0 = 0 is a proposition. So is the claim that 0 = 1.

As another example, in the domain of some family unit, a
perfectly good proposition is that "Mary is the mother of
Bob." It might or might not be true in a given family,
but it's a perfectly good proposition: a claim that a
certain state of affairs holds in that domain.

Logic, then, is about making propositions precise and
above precise rules for ascertaining when any given 
proposition can be judged to be true.

Clearly we would judge the proposition, 0 = 0, to be 
true, in the domain of arithmetic. Similarly, we would
not judge the proposition 0 = 1 to be true.

Logicians will sometimes write "0 = 0 : true" as a
way to assert that the proposition, 0 = 0, is (has
been judged to be) true. We call this a truth
judgment. More generally, if P is a proposition, 
then "P : true" denotes the judgment that P is true.

EXERCISE: Write a truth judgment (just type it
in as part of this comment) for the proposition
that "Mary is the mother of Bob."

Another example of a proposition is the claim that
zero does not equal one, which we would write like
this: ¬ (0 = 1). You could pronounce this as "it is
NOT the case that 0 = 1." We would naturally judge
this proposition to be true (albeit currently just
based on our intution, not on any specific rules).

EXERCISE: Write a truth judgment here (just type it
in as part of this comment) that expresses the 
judgement that ¬ (0 = 1) is true.

Propositions, then, are claims that certain states
of affairs hold, and logic provides us with rules
for determing when a given proposition is (can be
judged to be) true.

Propositions are basically declarative statements,
asserting that "such and such" is true. What makes
them, and logic, formal is that they have a precise 
syntax, or form, and a precise semantics, or meaning.


/- * syntax * -/

Just as with computer programs, there are strict
rules that define the forms that propositions can
take, i.e., their syntax. For example, 0 = 0 is a
syntactically well-formed proposition, but 00= is
not.

/- * semantics *-/

Moreover, propositions in a given logic also have
meanings, in that they can be judged to be true,
or not, in a given domain. For example "Mary is 
the mom of Bob" (perhaps written more formally as
mother_of(Mary,Bob) is a proposition that can be 
judged to be true in some domains (family units)
and not true in others. It's true in a domain in
which Mary really is the mother of Bob, and it is
not true otherwise. 

A proposition cannot generally be judged to be 
true or false on its own. Rather, it is judged 
in some domain: under an *interpretation* that 
explains what each symbol in the proposition is 
meant  to refer to. 

For example, we could judge "Mary is the mother 
of Bob" to be true if and only if "Mary" refers 
to some person, "Bob" refers to another person, 
and under some definition of what it means to 
be the mother of, that the person referred to 
as Mary really is the mother of that person 
referred to as Bob. 

When we talk about the semantics of a logic, we 
are talking about rules for determining when some
given proposition can be judged to be true with
respect to some particular interpretation that
"maps" the symbols in the proposition to things
in the domain of discourse.

The rules for determining whether a proposition 
in a particular logic is true in a given such a
domain and interpretation is, again, called the 
semantics of that logic.

Logics thus provide rules that define the syntax
and the semantics of propositions: their forms,
and their meanings (that is, whether they are,
i.e., can be judged to be, true or not) under 
any given interpretation.

We'll dive deeper into the syntax and semantics 
of various logics as we go along. In particular,
we will discuss a simple logic, propositional
logic, and a much more useful logic, the logic 
of everyday mathematics and computer science, 
called predicate logic.

For purposes of this unit, we'll just assume 
that one particular form of valid proposition 
in predicate logic is a proposition that the 
values of two terms are equal. For example, 
0 = 0, 1 + 1 = 2, and 1 + 1 = 3 are valid 
(syntactically well formed) propositions in 
the predicate logic of everyday mathematics
and computer science.
-/

/- ** Inference rules ** -/

/-
So how do we decide whether a given proposition
can be judged to be true or not? Here is where 
the semantics of a logic come into play.

The semantics of a logic comprises a set of rules,
called inference rules, that define the conditions 
under which a given proposition can be judged to 
be true.

Oversimplying a bit, if you can apply one or more 
inference rules to propositions you already know 
to be true, and if by doing this you "deduce" some
new proposition, then you can conclude that that
new proposition must also be true. Such a "chain"
of inference rules, linking things already known
to be true to propositions that you want to prove
to be true because they follow logically is called
a proof. A valid proof is incontrovertible evidence
that the final proposition is true.

An inference rule is like a little program: it says,
if you can give me evidence (i.e., proofs) showing
that certain "input" propositions can be judged to
be true, then I will hand you back evidence (i.e.,
a proof) that shows that some new proposition can 
also be judged to be true. We would say that from 
the  proofs of the premises (the input propositions
already known to be true), the rule derives or deduces
a proof of the conclusion.

Logicians often write inference rules like this:

  list of input truth judgments 
  ----------------------------- (name-of-rule)
  truth judgment for conclusion

The required input judgments, called premises (or
antecedents), are listed above the line. The name 
of the rule is given to the right of the line. And
the proposition (or consequent) that can thereby
be judged to be true (the conclusion of the rule)
is written below the line.

For example, if we already have the truth judgment,
(0 = 0 : true), and another, (1 = 1: true), then the 
inference rule that logicians call "and introduction"
(or "conjunction introduction") can be used to derive
a truth judgment for the new proposition, "0 = 0 and
1 = 1", typically written as 0 = 0 ∧ 1 = 1. (Hover
your mouse over special symbols in this editor to
learn how to use them in your work.)

Predicate logic will thus (in effect) include this 
rule as an inference rule:

0 = 0 : true, 1 = 1 : true
-------------------------- and-introduction-*
      0 = 0 ∧ 1 = 1

This can be pronounced as, "If you already have 
evidence (a proof) supporting the judgment that 
0 = 0 is true, and if you also have evidence (a
proof) supporting the judgment that 1 = 1 is true, 
then by applying the and-introduction-* rule, 
you can deduce (obtain a proof justifying a truth
judgment for) the proposition, 0 = 0 ∧  1 = 1". 

We've put a * on the name of this rule to indicate
that it's really just a special case of a far more
general inference rule for reasoning about equality. 

Inference rules are usually written not in terms of 
very specific propositions, such as 0 = 0, but in 
terms of variables that can refer to any arbitrary 
propositions. They are often called meta-variables.


In this way, inference rules become program-like, in
that they can take arbitrary inputs (of the correct 
types), and whenever they are given such inputs, they
produce result of a promised type.

Here's a simple example of such a parameterized and
thereby generalized rule. If P is *any* proposition 
(e.g., it could be 0 = 0 but might be some other
proposition), and Q is another proposition (e.g.,
1 = 1), and if both propositions are already known
to be true, then you can always conclude that the 
proposition "P and Q", written P ∧ Q, must also be
true, for whatever propositions P and Q happen to 
be.

Here is how the general form of this inference rule 
would typically be written in a book on logic.

P : true, Q : true
------------------ (and-introduction)
   P ∧ Q : true

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

To denote the fact that we have a proof, 
let's call it, p, of some proposition, P, 
we will write p : P. Now, the idea is that 
if we have p : P then we also have P : true, 
and the only way we can get P : true is if 
we have some evidence, p, (a proof) for P. 

In other words, P is true if and only if we 
have evidence (a proof), p, for P. We can 
write this statement in the language of logic
like this: "p : P ↔ P : true".  The evidence, 
p, for P, justifies the judgement, P : true,
and the only way to justify such a judgement
is with such a piece of evidence. The bottom
line: having a proof of P is equivalent to P 
being true.

We can thus write an equivalent inference 
rule like this (compare with the previous):

p : P, q : Q
------------ (and-introduction)
 r : P ∧ Q

This then says, "If you give me a proof, p, of
some proposition, P, and if you also given me a
proof, q, of some proposition Q, then I promise
to give you back a proof, r, of the proposition,
P ∧ Q." 

As a shorthand, logicians usually leave off the
": true" bits and/or the "p :" bits, and so you'd 
usually see this rule written simply like this:

   P, Q
   ----- and-introduction
   P ∧ Q

Above the line, then, is a list of propositions 
that must be true (i.e., for which there must
already be proofs) for the rule to be applied. Below 
the line is a new proposition, the conclusion, 
which typically involves some premise propositions.
An inference rule allows you to conlude that the
conclusion is true whenever you already know that
the premises are true. 

A nice way to think about such a rule is as a 
little program. Let's call it "and-introduction!" 
It takes two arguments: namely a proof, p, of P, 
and a proof, q, of Q. When these are provided as
arguments, the program constructs and returns a 
proof, r, of P ∧ Q. How it might do this and what 
such a proof might look like are details that we 
will get to shortly. 
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

/- *** Axioms *** -/

/-
In a mathematical or logical system, some propositions 
are taken to be true unconditionally: without the need 
for any prior "input" judgements or proofs.

An inference rule that requires no proof or truth
judgement inputs, and that nevertheless lets you 
judge some proposition to be true unconditionally,
(e.g., by simply handing you a proof of or a truth
judgment for that proposition), is called an axiom. 

We also use the term, axiom, to refer to the 
proposition that is the conclusion of the rule, 
and that is thereby judged true unconditionally. 

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

/- * Type judgments * -/

We meet a new kind of judgment here: a type judgment.
If X is some type, and x is a value of that type, X, 
we can denote this fact by writing x : X. We read this
as "x is of type X."



/- * The types of types * -/

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
So now, with all that out of the way, we can write
the inference rule for equality that we really want. 

T: Type, t : T
-------------- (eq)
    t = t

Those are now type judgments above the line. You can 
understand this inference rule as saying this: "if you 
give me a T that is a type (e.g., bool, nat, string), 
and if you also give me a value, t, of type, T, (e.g.,
0 or true), then I will give you back a proof that 
t = t. This single inference rule thus defines a very 
sensible notion of equality for all values of all types 
that exist or might ever be defined. 

(Detail: This notion of equality is called Leibniz
equality.)

EXERCISE: Why exactly can this rule never be used to 
derive a proof of the proposition that 0 = 1?

So now, rather than a separate axiom for 0 = 0,
another one for 1 = 1, another for true = true, and
yet another for Fido = Fido, so forth, we now have 
a single inference rule, which we take as an axiom
(no prior proofs are required, but the types of T
and t do have to be right) that covers every possible 
case, forever forward.  

/- * Formalizing Leibniz equality * -/

Now we move the ball forward yet another yard or two. 
In predicate logic, we could also write the inference 
rule for eq like this: ∀ T: Type, ∀ t: T, t = t. 

The upside-down A is called the universal quantifier 
of predicate logic. You can pronounce it as "for all" 
or "for any" or "if you give me any value of the given
type ..." Thus we have, "for any T of type, Type, ..."
and what then follows is a proposition in which T is
used. That following proposition also uses ∀. And the
proposition after that, t = t, is interpreted in a way
that assumes T and t have been given specific meanings
by the preceding quantifiers. We say that T and t are
"bound" in the expression, t = t. The scope of that
binding is limited to the current proposition.

You could thus pronounce the rule like this: "If you
give me any value, T, of type, Type (which is to say
that if T is any type), and if you give me any value,
t, of that type, T, then I promise to give you back 
a value of type t = t.

Wait! We expected to get back a proof of t = t.

Yeah! In the logic of Lean, propositions are types
and proofs are values of these types. To read the
rule again, we could say, if you given me any type,
T, and any value, t, of that type, I promise to give
you back a value of type, t = t. But t = t is clearly
a proposition, so a value of this type is ... wait for
it ... a proof: a proof of the proposition, t = t." 
-/

/-
Now, given this more general inference rule, we could
"apply" it to the case where T = nat (Lean's name for
the type of natural numbers), and where t = 0 (a value
of this type) to produce a proof of 0 = 0. We could 
apply the same  rule to derive truth judgements for 
1 = 1, 2 = 2, true = true, "Bob" = "Bob", and so on.
-/

/-
In Lean, this inference rule is built in (actually 
defined in a library that is automatically loaded 
when you start Lean). Moreover, there's a shorthand 
in Lean for applying this rule to a value, t, of 
some particular type, T, to produce a proof of 
t = t. The shorthand is called "rfl". It can be 
applied whenever you want to produce a proof that 
two terms are equal.

Here's an example for the proposition, 0 = 0. Note:
mathematicians will often use the term "theorem" for a
proposition for which there is a proof of its truth.
-/

theorem zeqz: 0 = 0 := rfl

/-
Let's decode that. First, it says we're about
to establish a theorem by stating a proposition
and by giving a proof. The name that we give to
our proposition is zeqz (any variable name not 
already in use would do). The proposition for
which we seek a truth judgment (proof) is 0 = 0. 
The := separates the proposition from code that
is intended to produce such a proof. The proof 
code here is simply rfl. This rfl "thing" in
turn looks at the value on the left side of the
equal sign. It finds 0. That's "t". rfl can then 
infer that that the type of t is nat. That's T.
Given T = nat and t = 0, rfl returns a proof of
(a truth judgment for) the proposition, t = t,
where t = 0, which is to say, a proof of 0 = 0.
Lean then checks that this is a valid proof for
the proposition to be proved (also 0 = 0), which
it is, so so Lean accepts the proof as valid,
and assigns the proof as the value of zeqz.
From this point forward, zeqz can be used as 
a proof -- justifying a truth judgment -- for 
the proposition, 0 = 0. 
-/

/-
EXERCISE: Try to use the same approach to prove
a "theorem" (call it zeqo) that 0 = 1. What goes 
wrong? Hover over the red squiggles to see the 
error messages say. They're cryptic, but we can 
puzzle out what it's saying more or less. First,
the one over the rfl says rfl is expected to be
a proof that something (here denoted as m_2) is
equal to itself, but it is given as a putative 
proof of 0 = 1, and that doesn't work because in
fact it's not the case that 0 = 1. In a funny way
Lean treats the proposition as a type and expects
the proof to be a value of that type. Here, rfl 
generates a proof of "type" 0 = 0, but the "type"
of this proof object doesn't work for the type
of the proposition to be proved, "0 = 1", so Lean
rejects the proof. The red line over the zeqo
then explains that you've promised to provide a
proof, but you haven't, and so the thing you said
would be a theorem hasn't actually been proven to
be one!
-/

/- * A brief aside about terminology *-/

/-
Note: The word "theorem" in mathematics is generally
used to mean an "important" proposition that has been
proved. The word lemma is used to mean a somewhat less 
important proposition that has been proved, often as
part of a larger proof of a more important theorem.
Mathematicians also use the word corrolary to refer
to a proposition the proof of which follows from the
proof of a more important theorem. You can read all
about the various words used to refer to things that
have been proved, or that are intended to be proved,
here: https://academia.stackexchange.com/questions/113819/is-it-acceptable-for-a-referee-to-suggest-changing-theorem-into-proposition.
For our purposes, we'll typically just use theorem.
-/

/-
For use in a few minutes, here's a similar 
theorem (proposition with a proof) for the
proposition that one equals one.
-/

theorem oeqo : 1 = 1 := rfl

/-
EXERCISE: Use the same approach to prove that
"hello" = "hello".
EXERCISE: Does this approach work to prove that
2 = 1 + 1? You'd think it should, but those are
two different expressions on each side of =. Try
it to see if rfl can be used to generate a proof
that 2 = 1 + 1. Call your proof teqopo (for two
equals one plus one).
-/


/-
As you have now seen, Lean's notion of equality
does not mean exact equality of expressions. It
means instead the equality of what two expressions
mean: equality of the values to which they "reduce"
when you "evaluate" them. We can prove 2 = 1 + 1
using rfl because the "literal expression", 2, 
reduces  to the value 2, and the function 
application expression, 1 + 1 (wherein the plus 
function is applied to the two arguments, 1 and 1) 
also reduces to (evaluates to) 2. Now you've got 
the same value on each side of the =, and rfl 
will generate a valid proof of that proposition.  
The Lean type checker then confirms that this proof
is of type 2 = 1 + 1, and Lean takes that proof to
be the value of teqopo.
-/

/- 
EXERCISE: Prove as a theorem, tthof (a silly and 
uninformative name to be sure), that 2 + 3 = 1 + 4.

EXERCISE: Prove as a theorem, hpleqhl, that "Hello " 
++ "Logic! is equal to "Hello Logic!" (these values 
are of type string in Lean and the ++ operator here 
refers to the string concatenation function in Lean.)
-/

/- *** Applying Inference Rules *** -/

/-
As a cherry on top, let's return to the idea of
inference rules that require prior proof judgments
of other propositions as inputs. What inference
rules do in general is to build bigger proofs
from smaller ones!

For example, we now have a proof, zeqz, for the 
proposition that 0 = 0, and we also have one, oeqo, 
for the proposition, 1 = 1. You'd think we might 
therefore be able to produce a new proof for the 
proposition that 0 = 0 ∧ 1 = 1.
-/

/-
EXERCISE: What inference rule might we try to apply
to generate such a proof? 
-/

/-
In Lean the and-introduction inference rule goes by
the name and.intro. It takes two arguments: a proof 
for any proposition, P, and a proof for another
proposition, Q. It then returns a proof for the 
proposition P ∧ Q. Here's the code!
-/

theorem zeqz_and_oeqo: 0 = 0 ∧ 1 = 1 := 
    and.intro zeqz oeqo -- study this carefully!

/-
Ok, let's decode that. We're proposing a theorem.
The proposition we aim to prove is 0 = 0 ∧ 1 = 1.
If we can generate a proof that Lean accepts, it
will become the value bound to zeqz_and_oeqo. 
Finally, we propose to generate this proof by 
applying the and introduction inference rule, which, 
again, in Lean, is called and.intro.

This rule, and.intro, is really just a function!
In Lean you apply a function to its arguments by 
first writing the function name and then writing 
each of the arguments following that name. You do
not write the arguments to a function as a list 
of values within parentheses as in Python or Java. 

Voilà! We apply an inference rule "program" to
two smaller proofs to get a larger one and then
Lean checks automatically to make sure it's a
valid proof for the proposition that was asserted.
It actually does this by checking to see if the
type of the proof is consistent with the type of
the proposition.
-/

/-
EXERCISE: What happens if the proofs you pass to 
and.intro aren't quite right? For example, try to 
give zeqz as the value for both arguments. Does the
resulting proof "type check"?
-/

/-
Suppose we wanted to prove a similar theorem for
the proposition that 2 = 2 ∧ "Hi" = "Hi". We can
of course write two smaller theorems for 2 = 2 
and "Hi" = "Hi". Each of these would in turn be
proved by the application of the rfl rule. Then 
we could use the named proofs as inputs to the
and.intro "rule" and we'd be done. But there's 
a shorter way to go: just write the proofs of 
the individual propositions directly inline.
The and.intro rule needs a proof of 2 = 2, and
rfl will do. Similarly it needs a proof of "Hi"
= "Hi", and once again, rfl will so.
-/

theorem teqt_and_heqh: 2 = 2 ∧ "Hi" = "Hi" :=
  and.intro rfl rfl 


/- ** Formal Systems ** -/
/-
A mathematical, or formal, system starts with a set 
of inference rules including axioms (with the condition 
that this starting point not be self-contradictory; so, 
for example, you would never want 0 = 1 as an axiom). 
It extends to include the typically infinite set of 
all of theorems that can be possibly "proved" by any
number of applications of available inference rules 
to already available truth judgments (or equivalently
to proofs, which in Lean are taken to be tantamount
to truth judgments).  
-/

/-
EXERCISE: What are some other theorems that you could
prove using only the concepts we've discussed so far?
Formulate and prove several new theorems. Note that 
Lean has a Boolean type, called bool, with the values
tt and ff (short for Boolean true and Boolean false).
Prove at least one theorem involving Boolean values.
-/

/- ** What mathematicians and some computer scientists do -/

/-
Working mathematicians and computer scientists don't sit
around all day mechanically generating theorems by applying
inference rules to already proved theorems to come up with
new theorems. That would be like typing randomly and hoping
to produce a new Shakespeare-quality play. 

Rather, mathematicians and computer scientists, come up
with propositions that they believe, and hope, are true
(e.g., a proposition that asserts that some program gives
the right answer for any possible combination of inputs);
and they then have the task of producing proofs to show
that such propositions are true.

We call this the problem of "proving" that a proposition
is true. If there is already a truth judgment for (proof 
of) the given proposition, it's easy: you just hand over
the existing proof. If there are proofs to which an
inference rule can be applied directly to produce a
proof for the given proposition, then you just apply the
inference rule to those proofs and you hand over the new
proof that results. In the typical case, you won't have
proofs of propositions that you need as inputs to the
inference rule that you'll ultimately want to generate
the desired proof, so you need to go off and produce
proofs of those intermediate propositions first. In this 
way the task of producing the desired proof is broken
down into one or more smaller problems of producing the
proofs that are needed to feed the inference rule that
will be used to produce the final proof. 

Mathematicians typically label the proposition that is
ultimately to be proved as a theorem (once there really
is a proof), and the smaller propositions to be proved
as lemmas. In Lean you can use theorem and lemma (and
a few other keywords, such as def) interchangeably.

Such a process is said to be "recursive". Axioms give
you starting points. You then apply inference rules to
produces proofs of larger and larger lemmas. Finally 
you apply some inference rule to proofs of key lemmas
to produce a proof of the desired theorem. 

The chain of "derivations" that thus results is what
logicians and mathematicians sometimes call a proof tree.
Such trees can be written using inference rule notation.

Here's the entire proof tree for 0 = 0 ∧ 1 = 1. 

 rfl     rfl
-----   -----
0 = 0   1 = 1
------------- 
0 = 0 ∧ 1 = 1

Read it from bottom to the top: to prove the desired
proposition, we need proofs of 0 = 0 and 1 = 1 
respectively. Each of these in turn can be produced 
by the rfl "axiom". These axioms requires no prior 
proofs (truth judgments) as inputs, so you are done. 
(We've left off the rule names to make the proof 
tree easier to read. Typically they'd be included.)

So, coming up with a proof of a proposition that hasn't 
yet been proved often feels like a "backwards chaining"
activity. When asked to prove a proposition, P, we often
try to find other propositions, such as Q and R, such that
if we had proofs of Q and R, we could then apply a valid 
inference rule to prove P. One thus reduces the problem 
of proving P to the sub-problems of proving Q and R. One 
then backward-chains this way until one finally reaches 
... axioms! Axioms are the "base cases" in the recursive
decomposition of the overall problem: there is no need
to recurse any further once you've reach the bottom!
-/

/-
EXERCISE: What "smaller" propositions might you want to
prove if your aim is ultimately to prove the proposition
that 5 = 1 + 4 ∧ "Strike" = "S" ++ "trike". Go ahead and
prove those smaller propositions. You can use whatever
names you want for these little "theorems", then write
the theorem that proves the final result using the lemmas
as inputs.
-/

/- ** Logical Foundations of Mathematics ** -/

/-
Modern mathematics is axiomatic. It's logical. It is
"founded" on mutually consistent axioms and inference
rules. 

There is however more than one way to establish the 
logical foundations of mathematics.

The most widely used axiomatic foundation comprises a
set of axioms that describes what it means to be a set,
and everything else then builds on the concept of sets.
The resulting theory is called "set theory." Set theory
is the most widely accepted and used logical foundation
for everyday mathematics.

The natural numbers for example can be "formalized" as
sets. Zero is represented by the empty set; one by the
set that contains only the empty set; two by the set
that contains that set; and so forth. 

The specific set theory foundation for ordinary
mathematics is known as Zermelo-Frankl Set Theory 
with the Axiom of Choice (often abbreviated as ZFC). 
The axioms of ZFC capture our "naïve" view of sets 
as collections of elements. It took much time and
great care, however, to craft a set of axioms that
are not self-contradicting. The original formulation
of set theory turned out to be inconsistent! 

(Does the set of all sets that do not contain 
themselves contain itself? If it does, then it 
doesn't, and if it doesn't then it does: a real 
inconsistency! In fact it was this problem that
led mathematicians to a much more careful notion
of what it means to be a set, as captured by the
axioms of ZFC.

As another example of an inconsistency, there's 
a word in the English language to describe words 
that describe themselves: autological. The antonym 
of autological is heterological. "Polysyllabic" is 
autological, but  "palindrome" is heterological. 
Is the word "heterological" heterological? If the 
word doesn't describe itself, then it is, but then 
the word would describe itself. So, yeah, English
is inconsistent in this sense.)

The axioms of ZFC are somewhat technical; we will 
not explore them in this class. What you might want
to remember is that if you want to prove even simple
mathematical proposition in a precise, fully formal 
way using ZFC, it is a complex and messy affair. 

In fact, it's so messy that most mathematicians trade
in rigorous but informal proofs. By informal 
proofs we mean mathematical arguments written in a 
stylized form of a natural language, such as English.
For example, a proof of 0 = 0 and 1 = 1 might read
like this: "To prove the proposition, which is a
conjunction, we need proofs of the two parts. The
first, 0 = 0, is proved by noting that equality is
a reflexive relation, and 1 = 1 is proved similarly.
Given that both conjuncts are so, then so is the
overall conjunction. So it is shown (QED in latin)."

Because machines aren't much good at figuring out what
natural language text means with mathematical precision, 
it's nearly impossible today for computers to check that
purported informal proofs are correct. Proof checking 
remains a demanding, mostly human, and social process. 

When a mathematician claims to have produced a proof
of a theorem of potential significance, other experts
come together (often as reviewers for journals to which
mathematical purported proofs are generally submitted 
for review and publication) to see if they can find 
any errors in reasoning. They often do! 

Such human proof checking has in some cases proved to 
be nearly intractable. For example, in 2012, Shinichi 
Mochizuki, a reclusive Japanse mathematician, quietly 
posted to the web a 500-page "putative" proof of a 
major mathematical conjecture (proposition for which
there is not yet a proof) in number theory and geometry.
If correct, it could revolutionize mathematics. Yet the 
work is so complex and unusual that the mathematical 
community even to this day has still been unable even 
to comprehend the overall concept, not to mention 
checking every last detail for subtle errors. 
-/

/- 
HOMEWORK: Read this article. https://www.sciencealert.com/nightmarish-500-page-math-proof-even-experts-can-t-understand-about-published-shinichi-mochizuki
-/

/-
An alternative foundation for mathematics (in particular
for what is called "constructive" mathematics) is available
in what is called "type theory." It's basically a different
(from ZFC) set of axioms and inference rules on which math 
can be based. Not surprisingly, types, rather than sets, are
a fundamental building block of mathematics in type theory.
Sets can be modeled, but they are not built in. 

From your high school math background, you probably 
already have a reasonable intuition for sets as collections
of values. A type also defines a set of values, and each
value in that set has that type. But whereas a value can be
in many sets, in type theory a value has exactly one type.
Whenever you see a value, or an expression that reduces to
a value, in type theory, it thus makes sense to ask the
question, what is its type? Every well formed expression
and value in a type theory has exactly one type. 

In Lean, we can ask the type of an expression (including
of a literal expression that directly denotes a value) by
using the check command. Hover your mouse over the #check
command. Note that ℕ is mathematical notation for "natural
number", the type of non-negative integers.
-/

-- The types of some literal expressions 
#check 0
#check "Hello"
#check tt

-- defining a binding of an identifier to a value
def foo := 0

-- The type of a variable expression
#check foo

-- The types of some more complex expressions
#check 1 + foo
#check "Hello " ++ "Logic!"
#check tt && ff

/-
Without getting into complicated details, it will suffice 
for now to say that proofs are much more tractable objects 
in type theory than in set theory. Type theory has thus 
emerged as an important framework for *automating* the 
handling of logic in both mathematics and computer science. 

For computer scientists, it is also the main foundation for
functional programming, the theory of programming languages, 
and for formal verification of software correctness, which
is vitally important when ultra-high levels of confidence 
in the correctness of code is required (e.g., for security). 

This very tool and language that you're using now, the Lean
prover, is based on type theory. It's am example of what's 
known in the business as a proof assistant. But you can just 
think of it for now as a really cool tool in which you can 
write both programs and logic, and that can help you to 
construct "manageable" proofs. Through the magic of type 
checking it then *automatically* determines whether a proof 
is valid for a given proposition.

This technology holds the promise of eventually changing
the way that code is written and verified, and even the way 
that mathematics work.
-/

/-
In this unit you've learned the following concepts:

* formal system
* proposition
* axiom
* inference rule
* truth judgment 
* proof
* equality
* type judgment
* set theory and type theory foundations of mathematics
* type theory for automating mathematical logic and proof checking
-/