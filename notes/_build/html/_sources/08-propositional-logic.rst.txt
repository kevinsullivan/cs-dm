**********************
8. Propositional Logic
**********************

A mathematical logic is defined by (1) a *syntax* that specifies the
set (usually infinite) of *well formed expressions* in the language
(also called *well formed formulae*, or *wffs*), and (2) a *semantics*
by which one can evaluate *truth value* of any such expression.

Each sentence in a logical language is intended to represent a *truth
claim*: an assertion, about the prevailing *state of affairs* in some
*domain of discourse* that is either true or false. Dafny *assertions*
are logical expressions in this sense: they assert that the state of a
program at a specific point in its execution has certain properties
(e.g., that the value of a loop index is greater than zero) , or that
a specific relationship always holds between the state of the program
before and after some code is run (e.g., pre- and post-conditions and
loop invariants).

To use a logic for practical purposes, one must (1) understand how to
represent states of affairs in the domain of discourse of interest as
expressions in the logical language of the logic, and (2) hae some
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


Introduction
============

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
=====

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

Interpretations
===============


Evaluate a Boolean expression in a given environment.  The recursive
structure of this algorithm reflects the inductive structure of the
expressions we've defined.

.. code-block:: dafny

    type interp = map<Bvar, bool>


Evaluation
==========

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
======


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
