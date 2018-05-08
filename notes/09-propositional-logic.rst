**********************
9. Propositional Logic
**********************

Here is a proposition: "Tom's mother is Mary." A proposition asserts
that a particular *state of affairs* holds in some particular *domain
of discourse*. The domain in this case would be some family unit; and
the state of affairs that is asserted to prevail is that Mary is Tom's
Mom.

Whether such a proposition can be *judged* to be *true* is another
matter. If the domain of discourse (or just *domain*) were that of a
family in which there really are people, Tom and Mary, and in that
family unity Mary really is the mother of Tom, then this proposition
could be judged to be true. However, if such a state of affairs did
not hold in that family unity, then the proposition would still be a
fine proposition, but it could not be judged to be true (and indeed
could be judged to be false).

In place of the phrase "domain of discourse" we could also use the
word, "world." In general, the truth of a proposition depends on the
world in which it is evaluated. There are some proposition that are
true in every world, e.g., "zero equals zero;" some that are not true
in any world, e.g., "zero equals one;" and many where the truth of the
proposition depends on the world in which it is evaluated, e.g., "Mary
is Tom's mother."

Logic is the discipline that studies such issues: what constitutes a
valid proposition, and when can we judge a proposition to be true?
The rest of this chapter introduces logic, in general, and what we
call propositional logic, in particular. Proposition logic is a simple
but useful logic that is very closely related to Boolean algebra. If
you understood the material on Boolean algebra, the transition to this
chapter should be very easy.


Propositional and Predicate Logic
=================================

The proposition, *Tom's mother is Mary*, is simple. It could even be
represented as a single variable, let's call it *M*.  In what we call
propositional logic, we generally represent propositions as variables
in this manner. Similarly, a logical variable, *F*, could represent
the proposition, *Tom's father is Ernst*.  We could then *construct* a
larger proposition by composing these two propositions into a larger
one under the logical connective called *and*. The result would be the
proposition, *Toms' mother is Mary and Tom's father is Ernst*. We
could of course write this more concisely as *M and F*, or, in a more
mathematical notation, :math:`M \land F`.

Now we ask, what is the truth value of this larger proposition? To
determine the answer, we conjoin the truth values of the constituent
propositions.  The meaning of the larger proposition is determined by
(1) the meanings of its smaller parts, and (2) the logical connective
that composes them into a larger proposition. For example, if it's
true that Tom's mother is Mary and it's also true that Tom's father is
Ernst, then the truth of the compound conjuction is *true and true*,
which is true. Such a logic of propositionsm their compositions into
larger propositions using connectives such as *and*, *or*, and *not*,
and this compositional way of determining the truth of propositions,
is called *propositional logic*.

By contrast, the proposition, "every person has a mother" (or to put
it more formally, :math:`\forall p \in Persons, \exists m \in Persons,
motherOf(p,m)`), belongs to a richer logic.  Here, *motherOf(p, m)* is
a *predicate on two values*. It stands for the family of propositions,
*the mother of p is m*, where *p* and *m* are variables that range
over the set of people in the given domain of discourse.  The overall
proposition thus asserts that, for *every* person, *p* in the domain,
there is a person, *m*, such that *m* is the mother of *p*.

The *motherOf(p,m)* construct is a *parameterized proposition*, which,
again, we call a *predicate*. You can think of it as a function that
takes two values, *p* and *m*, and that returns a proposition *about
those particular values*. A predicate thus represents not a just one
proposition but a whole *family* of propositions, one for each pair of
parameter values. Any particular proposition of this form might be
true or false depending on the domain of discourse. If *m* really is
the mother of *p* (in the assumed domain), then *motherOf(p,m)* can be
judged to be true (for that domain), and otherwise not.

Another way to look at a predicate is that it *picks out* a subset of
*(p,m)* pairs, namely all and only those for which *motherOf(p,m)* is
true. A predicate thus specifies a relation, here a binary relation,
namely the *motherOf* relation on the set of people in the domain of
discourse.

This richer logic, called *predicate logic*, (1) allows variables,
such as *p* and *m*, to range over sets of objects (rather that just
over Boolean values), (2) supports the expression predicates involving
elements of such sets, and (3) provides botg universal and existential
quantifiers (*for all* and *there exists*, respectively). As we will
see in a later chapter, a predicate logic also allows the definition
and use of functions taking arguments in the domain to identify other
objects in the domain. So, for example, a function, *theMotherOf*,
might be used to identify *Mary* as *theMotherOf(Tom)*. Note that when
a function is applied to domain values, the result is another domain
value, whereas when a predicate is applied to domain values, the
result is a proposition about those value.

Predicate logic is the logic of everyday mathematics and computer
science. It is, among other things, the logic Dafny provides for
writing specifications.  As an example, consider our specification of
what it means for a function, *R*, with domain, *D*, and codomain,
*C*, to be surjective: :math:`\forall c \in C, \exists d \in D, (d,c)
\in R`. In Dafny, we would (and did) write this as, *forall c :: c in
codom() ==> exists d :: d in dom() && (d,c) in rel().* Dafny is thus a
specification and verification system based on *predicate
logic*. We've been using it all along!

One of the main goals of this course up to now has been to get you
reading, writing, and seeing the utility of predicate logic. Far from
being an irrelevancy, it is one of the pillars of computer science. It
is a fundamental tool for specifying and reasoning about software.  It
is also central to artificial intelligence (AI), to combinatorial
optimization (e.g., for finding good travel routes), in the analysis
of algorithms, in digital circuit design, and in many other areas of
computer science, not to mention mathematics and mathematical fields
such as economics.

Going forward, one of our main goals is to understand predicate logic
in greater depth, including its syntax (what kinds of expressions can
you write in predicate logic?) its semantics (when are expressions in
predicate logic *true?*), and how to show that given expressions are
true.

In this chapter, which beings Part II of this set of notes, we start
our exploration of predicate logic and proof by first exploring the
simpler case of *propositional* logic.  To begin, in the next section,
we address the basic question, what is *a logic*, in the first place?

What is a Logic?
================

A logic is (1) a *formal language* of *propositions* along with (2)
principles for reasoning about whether any given proposition can be
judged to be *true* or not. A logic has a *syntax*, which is a set of
mathematically (formally) specified rules that precisely define the
set of well formed propositions (or *well formed formulae, or wffs*)
in the language. A logic also has a *semantics*, which is a set of
formal rules for reasoning about whether a given proposition can be
judged to be true or not.

In the last chapter, on Boolean algebra, we already saw what amounts
to a simplified version of propositional logic, with both a syntax and
a semantics! The syntax of our Boolean expression language is given by
the inductive *bExp* type.  It provides a set of constructors, which
are just the rules for building valid expressions, with an implicit
assumption that the valid expressions in the language are all and only
those that can be built using the provided constructors. The syntax is
compositional, in that smaller expressions can be composed into ever
larger ones, up to arbitrarily large (but always still finite) sizes.

The semantics of the simplified logic is then defined by a *semantic
evaluation* function, that takes *any* valid expression in the
language as an argument and that returns a Boolean value indicating
whether the given expression is (can be judged to be) true or not.
The semantics is also compositional in that the truth of a composed
proposition is defined recursively in terms of (1) the truth values of
its constituent propositions, and (2) the meaning of the connector
that was used to compose them. The recursive structure of semantic
evaluation exactly mirrors the inductive definition of the syntax.

Propositional Logic
===================

We now introduce propositional logic. The syntax of propositional
logic is basically that of our Boolean expression language with the
crucial addition of propositional *variable expressions*. Examples of
variable expressions include *M* and *F* in our example at the start
of this chapter. So, for example, in addition to being able to write
expressions such as *pAnd(pTrue,pFalse)*, we can write *pAnd(M,F)*,
where *M* and *F* are proposition variables that can have *true* or
*false* as their values.

As for semantics, propositional variables thus have Boolean values. To
evaluate a proposition in propositional logic, we thus ascertain the
Boolean value of each variable appearing in the proposition and then
proceed to evaluate the result just as we did with Boolean expression
evaluation in the last chapter. For example, if *M* is *true* and *F*
is *true*, then to evaluate *M and F*, we first evaluate each of *M*
and *F* individually, reducing the proposition to *true and true*. We
then reduce that expression using the rules for Boolean algebra. The
result in this case is, of course, just *true*.

The one complication, then, is that, to evaluate a proposition that
includes variables, our semantic evaluation function needs to have a
way to look up the Boolean value of each variable in the expression to
be evaluated. Our semantic evaluator needs a function, which could be
represented as a *map*, for example, from propositional variables such
as *M* and *F* to Boolean values.  Logicians call such a function an
*interpretation*. Programming language designers sometimes call it an
*environment*. To evaluate a variable expression, the evaluator will
just look up its value in the given intepretation and will otherwise
proceed as in the last chapter.


Syntax
======

A logic provides a *formal language* in which propositions (truth
statements) are expressed. By a formal language, we mean a (usually
infinite) set of valid expressions in the language. For example, the
language of Boolean expressions includes the expression *true and
false* but not *and or true not*.

When the set of valid expressions in a language is infinite in size,
it becomes impossible to define the language by simply listing all
valid expressions. Instead, the set of valid expressions is usually
defined *inductively* by a *grammar*. A grammar defines a set of
elementary expressions along with a set of rules for forming ever
larger expressions from ones already known to be in the language. We
also call the grammar for a formal language its *syntax*.

The syntax of proposition logic is very simple. First, (with details
that vary among presentations of propositional logic), it accepts two
*literal values*, usually called *true* and *false*, as expressions.
Here we will call these values *pFalse* and *pTrue* to emphasize that
these are *expressions* that we will eventually *interpret* as having
particular Boolean values (namely *false* and *true*, respectively).

Second, propositional logic assumes an infinite set of *propositional
variables*, each represents a proposition, and each on its own a valid
expression. For example, the variable, *X*, might represent the basic
proposition, "It is raining outside," and *Y*, that "The streets are
wet."  Such variables should be understood as being equated with basic
propositions. Instead of the identifier, *X*, one might just as well
have used the identifier, *it_is_raining_outside*, and for *Y*, the
identifier, *the_streets_are_wet*. 

Finally, in addition to literal values and propositional variables,
propositional logic provides the basic Boolean connectives to build
larger propositions from smaller ones. So, for example, *X and Y*, *X
or Y*, and *not X* are propositions constructed by the use of these
*logical connectives.* So is *(X or Y) and (not X)*. (Note that here
we have included parentheses to indicate grouping. We will gloss over
the parentheses as part of the syntax of propositional logic.) 

We have thus defined the entire syntax of propositional logic. We
can be more precise about the grammar, or syntax, of the language by
giving a more formal set of rules for forming expressions.

.. code-block:: BNF

   Expr       := Literal | Variable | Compound
   Literal    := pFalse | pTrue
   Variable   := X | Y | Z | ...
   Compound   := Not Expr | And Expr Expr | Or Expr Expr


This kind of specification of a grammar, or syntax, is said to be in
*Backus-Naur Form" or BNF, after the names of two researchers who were
instrumental in developing the theory of programming languages. (Every
programming language has such a grammar.)

This particular BNF grammar reads as follows. A legal expression is
either a literal expression, a variable expression, or a compound
expression.  A literal expression, in turn, is either *pTrue* or
*pFalse*. (Recall that these are not Boolean values but Boolean
*expressions* that *evaluate* to Boolean values.)  A variable
expression is X, Y, Z, or any another variable letter one might wish
to employ. Finally, if one already has an expression or two, one can
form a larger expression by putting the *Not* connective in front of
one, or an *And* or *Or* connective in front of two expressions.  That
is the entire grammar of propositional logic. (Some presentations of
propositional logic leave out the literal expressions, *pTrue* and
*pFalse*.)

Here's the corresponding completely formal code in Dafny. First, to
represent *variables*, we define a datatype called *propVar*, with a
single constructor called *mkPropVar*, that takes a single argument,
*name*, of type *string*.  Examples of variable objects of this type
thus include *mkPropVar("M")* and *mkPropVar("F")*. Two variables of
this type are equal if and only if their string arguments are equal.

.. code-block:: dafny

   datatype propVar = mkPropVar(name: string) 

With that, we can now give a Dafny specification of the syntax of our
version of propositional logic. It's exactly the same as the syntax of
Boolean expressions from the last chapter but for the addition of one
new kind of expression, a *variable expression*, which is built using
the *pVar* constructor applied to a *variable* (that is, a value of
type *propVar*).

.. code-block:: dafny

   datatype prop = 
      pTrue | 
      pFalse |
      pVar (v: propVar) |
      pNot (e: prop) |
      pAnd (e1: prop, e2: prop) |
      pOr (e1: prop, e2: prop) |
      pImpl (e1: prop, e2: prop)

This kind of definition is what we call an *inductive definition*. The
set of legal expressions is defined in part in terms of expressions!
It's like recursion. What makes it work is that one starts with some
non-recursive *base* values, and then the inductive rules allow them
to be put together into ever larger expressions. Thinking in reverse,
one can always take a large expression and break it into parts, using
recursion until base cases are reached.

Note that we distinguish *variables* (values of type *propVar*) from
*variable expressions* (values of type *prop*). This approach makes it
easy to represent an interpretation as a map from variables (of type
*propVar*) to Boolean values.

Semantics of Propositional Logic
================================

Second, a logic defines a of what is required for a proposition to be
judged true. This definition constitutes what we call the *semantics*
of the language. The semantics of a logic given *meaning* to what are
otherwise abstract mathematical expressions; and do so in particular
by explaining when a given proposition is true or not true.

The semantics of propositional logic are simple. They just generalize
the semantics of our Boolean expression language by also supporting the
evaluation of propositional variable expressions.

The literal expressions, *pTrue* and *pFalse* still evaluate to
Boolean *true* and *false*, respectively. A variable can have either
the value, *true* or the value, *false*. To evaluate the value of any
particular variable expression, one obtains the underlying variable
and looks up its Boolean values in a given *interpretation*.  Recall
that an interpretation is just a *map* (or *function*) from variables
to Boolean values. Finally, an an expression of the form *pAnd e1 e2*,
*pOr e1 e2*, or *pNot e* are evaluated just as they were in the last
chapter, by recursively evaluating the sub-expressions and combining
the values using the Boolean operator corresponding to the constructor
that was used to build the compound expression. Evaluation of a larger
expression is done by recursively evaluating smaller expressions until
the base cases of *pTrue* and *pFalse* are reached.

Here's the Dafny code for semantic evaluation of any proposition (an
expression object of type *prop*) in our propositional logic language.

.. code-block:: dafny

   function method pEval(e: prop, i: pInterpretation): (r: bool)
        requires forall v :: v in getVarsInProp(e) ==> v in i
    {
        match e 
        {
            case pTrue => true
            case pFalse => false
            case pVar(v: propVar) => pVarValue(v,i)
            case pNot(e1: prop) => !pEval(e1,i)
            case pAnd(e1, e2) => pEval(e1,i) && pEval(e2, i)
            case pOr(e1, e2) =>  pEval(e1, i) || pEval(e2, i)
            case pImpl(e1, e2) => pEval(e1, i) ==> pEval(e2, i)
        }
    }    

Our semantic evaluation function is called *pEval*. It takes a
proposition expression, $e$, and an interpration, *i*, which is just a
map from variables (of type *propVar*) to Boolean values, i.e., a
value of type *map<propVar,bool>*. The precondition is stated using an
auxiliary function we've define; and overall it simply requires that
there be a value defined in the map for any variable that appears in
the given expression, *e*. Finally, the evaluation procedure is just
as it was for our language of Boolean algebra, but now there is one
more rule: to evaluate a variable expression (built using the
*propVar* constructor), we just look up its value in the given map
(interpretation).

Exercise: Write a valid proposition using our Dafny implementation to
represent the assertion that *either it is not raining outside or the
streets are wet.* Use only one logical connective.

Exercise: Extend the syntax above to include an *implies* connective
and express the proposition from the previous exercise using it. (Okay,
the code already implements it, so this exercise is obsolete.)


Inference Rules for Propositional Logic
=======================================

Finally, a logic provides a set of *inference rules* for deriving new
propositions (conclusions) from given propositions (premises) in ways
that guarantee that if the premises are true, the conclusions will be,
too. The crucial characteristic of inference rules is that although
they are guarantee to *preserve meaning* (in the form of truthfulness
of propositions), they work entirely at the level of syntax.

Each such rule basically says, "if you have a set of premises with
certain syntactic structures, then you can combine them in ways to
derive new propositions with absolute certainty that, if the premises
are true, the conclusion will be, too.  Inference rules are thus rules
for transforming *syntax* in ways that are *semantically sound*. They
allow one to derive *meaningful* new conclusions without ever having
to think about meaning at all.

These ideas bring us to the concept of *proofs* in deductive logic. If
one is given a proposition that is not yet known to be true or not,
and a set of premises known or assumed to be true, a proof is simply a
set of applications of availabile inference rules in a way that, step
by step, connects the premises *syntactically* to the conclusion.

A key property of such a proof is that it can be checked mechanically,
without any consideration of *semantics* (meaning) to determine if it
is a valid proof or not. It is a simple matter at each step to check
whether a given inference rule was applied correctly to convert one
collection of propositions into another, and thus to check whether
*chains* of inference rules properly connect premises to conclusions.

For example, a simple inference rule called *modus ponens* states that
if *P* and *Q* are propositions and if one has as premises that (1)
*P* is true*, and (2) *if P is true then Q is true*, then one can
deduce that *Q is true*. This rule is applicable *no matter what* the
propositions *P* and *Q* are. It thus encodes a general rule of sound
reasoning.

A logic enables *semantically sound* "reasoning" by way of syntactic
transformations alone. And a wonderful thing about syntax is that it
is relatively easy to mechanize with software. What this means is that
we can implement systems that can reasoning *meaningfully* based on
syntactic transformation rules alone.

Note: Modern logic initially developed by Frege as a " formula
language for pure though,t modeled on that of arithmetic," and later
elaborated by Russel, Peano, and others as a language in which, in
turn, to establish completely formal foundations for mathematics.


Using Logic in Practice
=======================

To use a logic for practical purposes, one must (1) understand how to
represent states of affairs in the domain of discourse of interest as
expressions in the logical language of the logic, and (2) havee some
means of evaluating the truth values of the resulting expressions. In
Dafny, one must understand the logical language in which assertions
and related constructs (such as pre- and post-conditions) are written.

In many cases--the magic of an automated verifier such as Dafny--a
programmer can rely on Dafny to evaluate truth values of assertions
automatically. When Dafny is unable to verify the truth of a claim,
however, the programmer will also have to understand something about
the way that truth is ascertained in the logic, so as to be able to
provide Dafny with the help it might need to be able to complete its
verification task.

In this chapter, we take a major step toward understanding logic and
proofs by introducing the language *propositional logic* and a means
of evaluating the truth of any sentence in the language. The language
is closely related to the language of Boolean expressions introduced
in the last chapter. The main syntactic difference is that we add a
notion of *propositional variables*. We will defined the semantics of
this language by introducing the concept of an *interpration*, which
specifies a Boolean truth value for each such variable. We will then
evaluate the truth value of an expression *given an interpration for
the proposition variables in that expression* by replacing each of the
variables with its corresponding Boolean value and then using our
Boolean expression evaluator to determing the truth value of the
expression.

We will also note that this formulation gives rise to an important new
set of logical problems. Given an expression, does there exist an
interpretation that makes that expression evaluate to true? Do all
interpretations make it value to true? Can it be there there are no
interpretations that make a given expression evaluate to true?  And,
finally, are there *efficient* algorithms for *deciding* whether or
not the answer to any such question is yes or no.


Implementing Propositional Logic
================================

The rest of this chapter illustrates and further develops these ideas
using Boolean algebra, and a language of Boolean expressions, as a
case study in precise definition of the syntax (expression structure)
and semantics (expression evaluation) of a simple formal language: of
Boolean expressions containing Boolean variables.

To illustrate the potential utility of this language and its semantics
we will define three related *decision problems*. A decision problem
is a *kind* of problem for which there is an algorithm that can solve
any instance of the problem. The three decision problems we will study
start with a Boolean expression, one that can contain variables, and
ask where there is an assignment of *true* and *false* values to the
variables in the expression to make the overall expression evaluate to
*true*.

Here's an example. Suppose you're given the Boolean expression,
:math:`(P \lor Q) \land (\lnot R)`. The top-level operator is
*and*. The whole expression thus evaluates to *true* if and only if
both subexpressions do: :math:`(P \lor Q)` and :math:`\land (\lnot
R)`, respectively. The first, :math:`(P \lor Q)`, evaluates to *true*
if either of the variables, *P* and *Q*, are set to true. The second
evaluates to true if and only if the variable *R* is false. There are
thus settings of the variables that make the formula true. In each of
them, *R* is *false*, and either or both of *P* and *Q* are set to
true.

Given a Boolean expression with variables, an *interpretation* for
that expression is a binding of the variables in that expression to
corresponding Boolean values. A Boolean expression with no variables
is like a proposition: it is true or false on its own. An expression
with one or more variables will be true or false depending on how the
variables are used in the expression.

An interpretation that makes such a formula true is called a *model*.
The problem of finding a model is called, naturally enough, the model
finding problem, and the problem of finding *all* models that make a
Boolean expression true, the *model enumeration* or *model counting*
problem.

The first major *decision problem* that we identify is, for any given
Boolean expression, to determine whether it is *satisfiable*. That is,
is there at least one interpretation (assignment of truth values to
the variables in the expression that makes the expression evaluate to
*true*?  We saw, for example, that the expression, :math:`(P \lor Q)
\land (\lnot R)` is satifiable, and, moreover, that :math:`\{ (P,
true), (Q, false), (R, false) \}` is a (one of three) interpretations
that makes the expression true.

Such an interpretation is called a *model*. The problem of finding a
model (if there is one), and thereby showing that an expression is
satisfiable, is naturally enough called the* model finding* problem.

A second problem is to determine whether a Boolean expression is
*valid*. An expression is valid if *every* interpretation makes the
expression true. For example, the Boolean expression :math:`P \lor
\neg P` is always true. If *P* is set to true, the formula becomes
:math:`true \lor false`. If *P* is set to false, the formula is then
:math:`true \lor false`. Those are the only two interpretations and
under either of them, the resulting expression evaluates to true.

A third related problem is to determine whether a Boolean expression
is it *unsatisfiable*? This case occurs when there is *no* combination
of variable values makes the expression true. The expression :math:`P
\land \neg P` is unsatisfiable, for example. There is no value of $P$
(either *true* or *false*) that makes the resulting formula true.

These decision problems are all solvable. There are algorithms that in
a finite number of steps can determine answers to all of them. In the
worst case, one need only look at all possible combinations of true
and false values for each of the (finite number of) variables in an
expression. If there are *n* variables, that is at most :math:`2^n`
combinations of such values. Checking the value of an expression for
each of these interpretations will determine whether it's satisfiable,
unsatisfiable, or valid. In this chapter, we will see how these ideas
can be translated into runnable code.

The much more interesting question is whether there is a fundamentally
more efficient approach than checking all possible interpretations: an
approach with a cost that increases *exponentially* in the number of
variables in an expression. This is the greatest open question in all
of computer science, and one of the greatest open questions in all of
mathematics.

So let's see how it all works. The rest of this chapter first defines
a *syntax* for Boolean expressions. Then it defines a *semantics* in
the form of a procedure for *evaluating* any given Boolean expression
given a corresponding *interpretation*, i.e., a mapping from variables
in the expression to corresponding Boolean values. Next we define a
procedure that, for any given set of Boolean variables, computes and
returns a list of *all* interpretations. We also define a procedure
that, given any Boolean expression returns the set of variables in the
expression. For ths set we calculate the set of all interpretations.
Finally, by evaluating the expression on each such interpretation, we
decide whether the expression is satisfiable, unsatisfiable, or valid.

Along the way, we will meet *inductive definitions* as a fundamental
approach to concisely specifying languages with a potentially infinite
number of expressions, and the *match* expression for dealing with
values of inductively defined types. We will also see uses of several
of Dafny's built-in abstract data types, including sets, sequences,
and maps. So let's get going.


Syntax
------

Any basic introduction to programming will have made it clear that
there is an infinite set of Boolean expressions. First, we can take
the Boolean values, *true* and *false*, as *literal* expressions.
Second, we can take *Boolean variables*, such as *P* or *Q*, as a
Boolean *variable* expressions. Finally, we take take each Boolean
operator as having an associated expression constructor that takes one
or more smaller *Boolean expressions* as arguments.

Notice that in this last step, we introduced the idea of constructing
larger Boolean expressions out of smaller ones. We are thus defining
the set of all Boolean expressions *inductively*. For example, if *P*
is a Boolean variable expression, then we can construct a valid larger
expression, :math:`P \land true` to express the conjunction of the
value of *P* (whatever it might be( with the value, *true*. From here
we could build the larger expression, *P \lor (P \land true)*, and so
on, ad infinitum.

We define an infinite set of "variables" as terms of the form
mkVar(s), where s, astring, represents the name of the variable. The
term mkVar("P"), for example, is our way of writing "the var named P."

.. code-block:: dafny

    datatype Bvar = mkVar(name: string) 


Here's the definition of the *syntax*:

.. code-block:: dafny

    datatype Bexp = 
        litExp (b: bool) | 
        varExp (v: Bvar) | 
        notExp (e: Bexp) |
        andExp (e1: Bexp, e2: Bexp) |
        orExp (e1: Bexp, e2: Bexp)

Boolean expresions, as we've defined them here, are like propositions
with paramaters. The parameters are the variables. Depending on how we
assign them *true* and *false* values, the overall proposition might be
rendered true or false.

Interpretation
--------------


Evaluate a Boolean expression in a given environment.  The recursive
structure of this algorithm reflects the inductive structure of the
expressions we've defined.

.. code-block:: dafny

    type interp = map<Bvar, bool>


Semantics
---------

.. code-block:: dafny

    function method Beval(e: Bexp, i: interp): (r: bool) 
    {
        match e 
        {
            case litExp(b: bool) => b
            case varExp(v: Bvar) => lookup(v,i)
            case notExp(e1: Bexp) => !Beval(e1,i)
            case andExp(e1, e2) => Beval(e1,i) && Beval(e2, i)
            case orExp(e1, e2) =>  Beval(e1, i) || Beval(e2, i)
        }
    }    
}


Lookup value of given variable, v, in a given interpretation, i. If
there is not value for v in i, then just return false. This is not a
great design, in that a return of false could mean one of two things,
and it's ambiguous: either the value of the variable really is false,
or it's undefined.  For now, though, it's good enough to illustate our
main points.

.. code-block:: dafny

    function method lookup(v: Bvar, i: interp): bool
    {
        if (v in i) then i[v]
        else false
    }

Now that we know the basic values and operations of Boolean algebra,
we can be precise about the forms of and valid ways of transforming
*Boolean expressions.* For example, we've seen that we can transform
the expression *true and true* into *true*. But what about *true and
((false xor true) or (not (false implies true)))*?

To make sense of such expressions, we need to define what it means for
one to be well formed, and how to evaluate any such well formed
expressions by transforming it repeatedly into simpler forms but in
ways that preserve its meaning until we reach a single Boolean value.

Models
------


Satisfiability, Validity
========================

We can now characterize the most important *open question* (unsolved
mathematical problem) in computer science.  Is there an *efficient*
algorithm for determining whether any given Boolean formula is
satisfiable?

whether there is a combination of Boolean
variable values that makes any given Boolean expression true is the
most important unsolved problem in computer science. We currently do
not know of a solution that with runtime complexity that is better
than exponential the number of variables in an expression.  It's easy
to determine whether an assignment of values to variables does the
trick: just evaluate the expression with those values for the
variables. But *finding* such a combination today requires, for the
hardest of these problems, trying all :math:``2^n`` combinations of
Boolean values for *n* variables.

At the same time, we do not know that there is *not* a more efficient
algorithm. Many experts would bet that there isn't one, but until we
know for sure, there is a tantalizing possibility that someone someday
will find an *efficient decision procedure* for Boolean satisfiability.

To close this exploration of computational complexity theory, we'll
just note that we solved an instances of another related problem: not
only to determine whether there is at least one (whether *there
exists*) at least one combination of variable values that makes the
expression true, but further determining how many different ways there
are to do it.

Researchers and advanced practitioners of logic and computation
sometimes use the word *model* to refer to a combination of variable
values that makes an expression true. The problem of finding a Boolean
expression that *satisfies* a Boolean formula is thus somtetimes
called the *model finding* problem. By contrast, the problem of
determining how many ways there are to satisfy a Boolean expression is
called the *model counting* problem.

Solutions to these problems have a vast array of practical uses.  As
one still example, many logic puzzles can be represented as Boolean
expressions, and a model finder can be used to determine whether there
are any "solutions", if so, what one solution is. 

Logical Consequence
===================

Finally, logic consequence. A set of logical propositions, premises,
is said to entail another, a conclusion, if in every interpretation
where all of the premises are true the conclusion is also true. See
the file, consequence.dfy, for a consequence checker that works by
exhaustive checking of all interpretations. <More to come>.
