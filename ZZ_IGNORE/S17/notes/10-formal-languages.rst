*****************
 Formal Languages
*****************

In this chapter, we introduce the concept of formal languages. A
formal language is a set of expressions and corresponding meanings,
where the permitted forms of the expressions and the meaning of each
well formed expression is specified with mathematical precision.  The
ideas are simple and beautiful. We introduce them with a case study of
Boolean expressions, starting with a highly simplied language with
only two literal value expressions; then extending to a language that
adds the usualy Boolean connectives (and, or, not, etc).

Boolean Algebra Revisited
=========================

Any introduction to programming will have made it clear that there is
an infinite set of Boolean expressions. For example, in Dafny, *true*
is a Boolean expression; so are *false*, *true || false*, *(true ||
false) && (!false)*, and one could keep going on forever.

Boolean *expressions*, as we see here, are a different kind of thing
than Boolean *values*. There are only two Boolean values, but there is
an infinity of Boolean expressions. The connection is that each such
expression has a corresponding Boolean truth value. For example, the
expression, *(true || false) && (!false)* has the value, *true*.

The set of valid Boolean expressions is defined by the *syntax* of the
Boolean expression language. The sequence of symbols, *(true || false)
&& (!false)*, is a valid expression in the language, for example, but
*)( true false()||) false !&&* is not, just as the sequence of words,
"Mary works long hours" is a valid sentence in the English language,
but "long works hours Mary" isn't.

The syntax of a language defines the set of valid sentences in the
language. The semantics of a language gives a meaning to each valid
sentence in the language. In the case of Boolean expressions, the
meaning given to each valid "sentence" (expression) is simply the
Boolean value that that expression *reduces to*.

As an example of syntax, the *true*, in the statement, *var b :=
true;* is a valid expression in the language of Boolean expressions,
as defined by the *syntaxt* of this language. The semantics of the
language associates the Boolean *value*, *true*, with this expression.

You probably just noticed that we used the same symbol, *true*, for
both an expression and a value, blurring the distinction between
expressions and values. Expressions that directly represent values are
called *literal expressions*. Many languages use the usual name for a
value as a literal expression, and the semantics of the language then
associate each such expression with its corresponding value.

In the semantics of practical formal languages, literal expressions
are assigned the values that they name. So the *expression*, *true*,
means the *value*, *true*, for example. Similarly, when *3* appears on
the right side of an assignment/update statement, such as in *x := 3*,
it is an *expression*, a literal expression, that when *evaluated* is
taken to *mean* the natural number (that we usually represent as) *3*.

As computer scientists interested in languages and meaning, we can
make these concepts of syntax and semantics not only precisely clear
but also *runnable*. So let's get started.

In the rest of this chapter, we use the case of Boolean expressions to
introduce the concepts of the *syntax* and the *semantics* of *formal
languages*. The syntax of a formal language precisely defines a set of
*expressions* (sometimes called sentences or formulae). A *semantics*
associates a *meaning*, in the form of a *value*, with each expression
in the language.

A Very Simple Language of Boolean Expressions
=============================================

We start by considering a simplified language of Boolean expressions:
one with only two literal expressions, for *true* and *false* values,
along with several of the usual logical connectives.  To make it clear
that the literal expressions are not themselves Boolean values but
expressions that we will eventually interpret as meaning Boolean
values, we will call the literal values in our language not *true* and
*false* but *bTrue* and *bFalse*.

Syntax: Inductive Data Type Definitions
---------------------------------------

We can represent the syntax of this language in Dafny using what we
call an *inductive data type definition.* A data type defines a set of
values. So what we need to define is a data type whose values are all
and only the valid expressions in the language. The data type defines
the *syntax* of the language by specifying precisely the set of terms
that encode syntactically correct expressions in the language. Here we
see a key idea in computer science: programs (in this case simplified
Boolean expressions) are just data values, too.

So here we go. We need a type with only two values, each one of them
representing a valid expression in our language. Here's how we'd write
it in Dafny.

.. code-block:: dafny

   datatype Bexp =
	bTrue |
	bFalse

The definition starts with the *datatype* keyword, followed by the
name of the type being defined (*Bexp*, short for Boolean expression)
then an equals sign, and finally a list of *constructors* separated by
vertical bar characters. The constructors define the ways in which the
values of the type (or *terms*) can be created. Each constructor has a
and can take optional parameters. Here the names are *bTrue* and
*bFalse* and neither takes any parameters.

The only values of an inductive type are those that can be built using
the provided constructors. So the language that we have specified thus
far has only two values, which we take to be the valid expressions in
the language we are specifying, namely *bTrue* and *bFalse*.  That is
all there is to specifying the *syntax* of our simplified language of
Boolean expressions.

Semantics: Pattern Matching on Terms
------------------------------------

We now specify a semantics for this language. Speaking informally, we
want to associate, to each of the expressions in our simple two-term
language, a correponding meaning in the form of a Boolean value.  We
do this here by defining a function that takes an expression (a value
of type *bExp*) as an argument and that returns the Boolean *value*:
the *meaning* of that expression.  In particular, we want a function
that returns Dafny's Boolean value *true* for the expression, *bTrue*,
and the Boolean value *false* for *bFalse*.

Our implementation of such a function uses a new programming mechanism
that you probably haven't seen before, called *pattern matching*. The
idea is that when given a term, a Boolean expression in this case, the
code will look to see how that term was constructed, and it will
behave in different ways depending on the result of that
analysis. Here, the code matches on a given term to determine whether
it was constructed by the *bTrue* or by the *bFalse* constructor, and
it then returns what we want it to return as the corresponding Boolean
value. Here's the code in Dafny.

.. code-block:: dafny

   function method bEval(e: bExp): bool 
   {
     match e
     {
         case bTrue => true
         case bFalse => false
     }
   }
		
As a shorhand for *Boolean semantic evaluator* we call it *bEval*. It
takes an expression (a value of type, *bExp*) and returns a Boolean
value.  The function implementation uses an important construct that
is probably new to most readers: a *match* expression. What a match
expression does is to: first determine how a value of an inductive
type was buit, namely what constructor was used and what arguments
were provided (if any) and then to compute a result for the case at
hand.

The match expression starts with the match keyword followed by the
variable naming the value being matched. Then within curly braces
there is a *case* for each constructor for the type of that value.
There are two constructors for the type, *bExp*, so there are two
cases. Each case starts with the *case* keyword, then the name of a
constructor followed by an argument list if the construtor took
parameters. Neither constructor took any parameters, so there is no
need to deal with parameters here. The left side thus determines how
the value was constructed. Each case has an arrow, *=>*, that is
followed by an expression that when evaluated yields the result *for
that case*.

The code here can thus be read as saying, first look at the given
expression, then determine if it was *bTrue* or *bFalse*. In the first
case, return *true*. In the second case, return *false*. That is all
there is to defining a semantics for this simple language.


Extending the Language with Boolean Connectives
===============================================

So far our Boolean language is very uninteresting. There are only two
expressions in our language, two literal expressions, and all they
mean are their corresponding Boolean values. In this section of this
chapter, we see how to explode the situation dramatically by allowing
larger expressions to be built from smaller ones and the meanings of
larger expressions to be defined in terms of the meanings of their
parts. We see the use of true *inductive definitions* and *structural
recursions* to define the syntax and semantics of a language with an
infinite number of terms. 

In this case, these terms are expressions such as *(bTrue and (not
bFalse))*. In other words, we extend our language with the usual
Boolean connectives. These connectives allow arbitrary expressions to
be combined into ever larger expressions, without bound. Then the
challenge is to specify a meaning for every such expression.  We do
that by using recursion over the *structure* of any such term.


Inductive Definitions: Building Bigger Expressions from Smaller Ones
--------------------------------------------------------------------

The real language of Boolean expressions has many more than two valid
expressions, of course. In Dafny's Boolean expression sub-language,
for example, one can write not only the literal expressions, *true*
and *false*, but also expressions such as *(true || false) && (not
false)*.

There is an infinity of such expressions, because given any one or two
valid expressions (starting with *true* and *false*) we can always
build a bigger expression by combing the two given ones with a Boolean
operator. No matter how complex expressions *P* and *Q* are, we can,
for example, always form the even more complex expressions, *!P*, *P
&& Q*, and *P || Q*, among others.

How can we extend the syntax of our simplified language so that it
specifies the infinity set of well formed expressions in the language
of Boolean expressions? The answer is that we need to add some more
cosntructors. In particular, for each Boolean operator (including
*and, or*, and *not*), we need a a constructor that takes the right
number of smaller expressions as arguments and the builds the right
larger expression.

For example, if *P* and *Q* are arbitrary "smaller" expressions, we
need a consructor to build the expression *P and Q*, a constructor to
build the expression, *P or Q*, and one that can build the expressions
*not P* and *not Q*. Here then is the induction: some constructors of
the *bExp* type will take values of the very type we're defining as
parameters. And because we've defined some values as constants, we
have some expressions to get started with. Here's how we'd write the
code in Dafny.

.. code-block:: dafny

   datatype bExp = 
        bTrue |
        bFalse | 
        bNot (e: bExp) |
        bAnd (e1: bExp, e2: bExp) |
        bOr (e1: bExp, e2: bExp)

We've added three new constructors: one corresponding to each of the
*operator* in Boolean algebra (to keep things simple, we're dealing
with only three of them here). We have named each constructor in a way
that makes the connection to the corresponding operator clear.

We also see that these new constructors take parameters. The *bNot*
constructor takes a "smaller" expression, *e*, and builds/returns the
expression, *bNot e*, which we will interpret as *not e*, or, as we'd
write it in Dafny, *!e*. Similarly, given expressions, *e1* and *e2*,
the *bAnd* and *bOr* operators construct the expressions *bAnd(e1,e2)*
and *bOr(e1,e2)*, respectively, representing *e1 and e2* and *e1 or
e2*, respectively, or, in Dafny syntax, *e1 && e2* and *e1 || e2*.

An expression in our *bExp* language for the Dafny expression *(true
|| false) and (not false))* would be written as *bAnd( (bOr (bTrue,
bFalse)), (bNot bFalse))*. Writing complex expressions like this in
a single line of code can get awkward, to we could also structure the
code like this:

.. code-block:: dafny

   var T: bExp := bTrue;
   var F:      := bFalse;
   var P:      := bOr ( T,  F );
   var Q       := bNot ( F );
   var R       := bAnd ( P, Q );


Structural Recursion: The Meanings of Wholes from the Meanings of Parts
-----------------------------------------------------------------------

The remaining question, then, is how to give meanings to each of the
expressions in the infinite set of expressions that can be built by
finite numbers of applications of the constructor of our extended
*bExp* type? When we had only two values in the type, it was easy to
write a function that returned the right meaning-value for each of the
two cases. We can't possibly write a separate case, though, for each
of an infinite number of expressions. The solution lies again in the
realm of recursive functions.

Such a function will simply do mechanically what you the reader would
do if presented with a complex Boolean expression to evaluate.  You
first figure out what operator was applied to what smaller expression
or expressions. You then evaluate those expressions to get values for
them. And finally you apply the Boolean operator to those values to
get a result.

Take the expression, *(true || false) and (not false))*, which in our
language is expressed by the term, *bAnd( (bOr (bTrue, bFalse)), (bNot
bFalse))*. First we identify the *constructor* that was used to build
the expression In this case it's the constructor corresponding to the
*and* operator: *&&* in the Dafny expression and the *bAnd* in our own
expression language. What we then do depends on what case has occured.

In the case at hand, we are looking at the constructor for the *and*
operator. It took two smaller expressions as arguments. To enable the
precise expression of the return result, ew given temporary names to
the argument values that were passed to the constructor. We can call
them *e1* and *e2*, for example. 
sub-expressions that the operator was applied to.

In this case, *e1* would be *(true || false)* and *e2* would be *(not
false)*. To compute the value of the whole expression, we then obtain
Boolean values for each of *e1* and *e2* and then combine them using
the Boolean *and* operator.

The secret is that we get the values for *e1* and *e2* by the very
same means: recursively! Within the evaluation of the overall Boolean
expression, we thus recursively evaluate the subexpressions. Let's
work through the recursive evaluation of *e1*. It was built using the
*bOr* constructor. That constructor took two arguments, and they were,
in this instance, the literal expressions, *bTrue* and *bFalse*. To
obtain an overall result, we recursively evaluate each of these
expressions and then combine the result using the Boolean *or*
operator. Let's look at the recursive evaluation of the *bTrue*
expression. It just evaluates to the Boolean value, *true* with no
further recursion, so we're done with that. The *bFalse* evaluates to
*false*. These two values are then combined using *or* resulting in
a value of *true* for *eq*. A similarly recursive process produces
the value, *true*, for *e2*. (Reason through the details yourself!)
And finally the two Boolean values, *true* and *true* are combined
using Boolean *and*, and a value for the overall expression is thus
computed and returned.

Here's the Dafny code.

.. code-block:: dafny

    function method bEval(e: bExp): (r: bool) 
    {
        match e 
        {
            case bTrue => true
            case bFase => false
            case bNot(e: bExp) => !bEval(e)
            case bAnd(e1, e2) => bEval(e1) && bEval(e2)
            case bOrEe1, e2) =>  bEval(e1) || bEval(e2)
        }
    }    

This code extends our simpler example by adding three cases, one for
each of the new constructor. These constructors took smaller
expression values as arguments, so the corresponding cases have used
parameter lists to temporarily give names (*e1*, *e2*, etc.) to the
arguments that were given when the constructor was orginally used.
These names are then used to write the expressions on the right sides
of the arrows, to compute the final results.

These result-computing expressions use recursive evalation of the
constitute subexpressions to obtain their meanings (actual Boolean
values in Dafny) which they then combine using actual Dafny Boolean
operators to produce final results.

The meaning (Boolean value) of any of the infinite number of Boolean
expressions in the Boolean expression language defined by our syntax
(or *grammar*) can be found by a simple application of our *bEval*
function. To compute the value of *R*, above, for example, we just run
*bEval(R)*. For this *R*, this function will without any doubt return
the intended result, *true*.

Formal Languages
================

Formal languages are sets of well formed expressions with precisely
specified syntaxes and semantics.  Programming languages are formal
languages. Expressions in these languages are programs. The syntax of
a programming language specified what forms a program can take.  The
semantics of a programming language defines the computation that any
syntactically correct program describes. At the heart of a semantics
for a programming language is the specification, possibly in the form
of an implementation, of a *relation* associating programs, the input
values they receive, and the output values they produce, if any, when
given those inputs.

Logics are formal languages, too. We have now seen how to precisely
specify, and indeed implement, both the syntax and the semantics of
one such logic, namely propositional logic. This logic is isomorphic
in syntax and semantics to the language of Boolean expressions with
variables. We used an *inductive definition* of a type to specify and
implement the syntax, and a *structural recursion* to specify and to
implement the semantics, of our version of propositional logic.

In Dafny, we have also seen how to *use* first-order predicate logic
to write specifications. Indeed Dafny brings together three formal
languages in one: a language of pure functional programs, which can be
use to write both specifications and implementations; a language of
imperative programs, which can be used to write efficient code; and
first-order predicate logic for writing specifications. This logic
allows us to write propositions that constrain and relate the states
of imperative programs: e.g., to specify that if a program is run in a
state that satisfies a given pre-condition, and if it terminates, that
it will terminate in a state that satisfies a given post-condition.

In other words, the semantics of programs specify how programs define
relations on states. A given state pair *(S, T)* is in the relation
specified by a program *P* if whenever *S* satisfies the pre-condition
for *P*, running *P* with the input *S* can produce *T* as a result.

Syntax defines legal expressions. Semantics give each legal expression
a meaning. Programming languages and logics are formal languages. The
meaning of a program is a computation, understood (at least partly) in
terms of a relation on states.

The meaning of a logical proposition, on the other hand, is a mapping
from interpretations to truth values. Given a proposition, and then
given an interpretation, a proposition purports to describe a state of
affairs that holds in that interpetation. If that state of affairs can
be shown to hold, then the proposition can be judged to be true. There
are many kinds of logic. We've implemented a syntax and semantics for
proposition logic. We've used first-order predicate logic extensively
to write specifications, which Dafny verifies (mostly) automatically.
Going forward, we will take a deeper dive into first-order predicate
logic, and then, ultimately, into the higher-order logic of a modern
*proof assistant*. Even more interesting things are coming soon.



