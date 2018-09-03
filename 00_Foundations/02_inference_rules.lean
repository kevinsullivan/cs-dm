/- ** Inference rules ** -/

/-
So how do we decide whether a given proposition
can be judged to be true or not? Here is where 
the semantics of a logic come into play.

The semantics of a logic comprises a set of rules,
called inference rules, that define the conditions 
under which a given proposition can be judged to 
be true.

Oversimplifying a bit, if you can apply one or more 
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

Predicate logic will thus (in effect) include such
inference rules as this:

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
-/