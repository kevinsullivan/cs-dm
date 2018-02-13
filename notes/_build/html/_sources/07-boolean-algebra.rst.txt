********************************
7. Toward Logic: Boolean Algebra
********************************

As a stepping stone toward a deeper exploration of deductive logic, we
explore the related notion of Boolean *algebra*.  Boolean algebra is
akin to ordinary high school algebra, and as such, deals with values,
variables, and functions.  However, the values in Boolean algebra are
limited to the two values in the set, :math:`bool = \{ 0, 1\}`. Based
on the connection between Boolean algebra and *propositional logic*,
these values are often written as *false* and *true*, respectively.

The *bool* Type in Dafny
========================

All general-purpose programming languages support Boolean
algebra. Dafny does so through its *bool* data type and the
*operators* associated with it. Having taking a programming course,
you will already have been exposed to all of the important ideas.
Here's a (useless) Dafny method that illustrates how Boolean values
can be used in Dafny. It presents a method, $BoolOps$, that takes a
Boolean value and returns one. The commands within the method body
illustrate the use of Boolean constant values and unary and binary
operators provided by the Dafny language. 

.. code-block:: dafny

   method BoolOps(a: bool) returns (r: bool)  
   {
       var t: bool := true;    // explicit type declaration
       var f := false;         // type inferred automatically
       var not := !t;          // negation
       var conj := t && f;     // conjunction, short-circuit evaluation
       var disj := t || f;     // disjunction, short-circuit (sc) evaluation
       var impl := t ==> f;    // implication, right associative, sc from left
       var foll := t <== f;    // follows, left associative, sc from right
       var equv := t <==> t;   // iff, bi-implication
       return true;            // returning a Boolean value
    }


The first line assigns the Boolean constant, *true*, to a Boolean
variable, *t*, that is explicitly declared to be of type,, *bool*.
The second line assigns the Boolean constant, *false*, to *f*, and
allows Dafny to infer that the type of *f* must be *bool*, based on
the type of value being assigned to it. The third line illustrates the
use of the *negation* operator, denoted as *!* in Dafny. Here the
negation of *t* is assigned to the new Boolean variable, *not*. The
next line illustrates the use of the Boolean *and*, or *conjunction*
operator (*&&*). Next is the Boolean *or*, or *disjunction*, operator,
(*||*). These should all be familiar.

Implication (*==>*) is a binary operator (taking two Boolean values)
that is read as *implies* and that evaluates to false only when the
first argument is true and the second one is false, and that evaluates
to true otherwise. The *follows* operator (*<==*) swaps the order of
the arguments, and evaluates to false if the first argument is false
and the second is true, and evaluates to true otherwise. Finally, the
*equivalence* operator evaluates to true if both arguments have the
same Boolean value, and evaluates to false otherwise. These operators
are especially useful in writing assertions in Dafny.

The last line returns the Boolean value true as the result of running
this method. Other operations built into Dafny also return Boolean
values.  Arithmetic comparison operators, such as *<*, are examples.
The less than operator, for example, takes two numerical arguments and
returns true if the first is strictly less than the second, otherwise
it returns false.

Boolean Algebra
===============


Boolean algebra is an algebra, which is a set of values and of
operations that take and return these values. The set of values in
Boolean algebra, is just the set containing *0* and *1*.

.. math::

   bool = \{ 0, 1 \}.

In English that expression just gave a name that we can use, *bool*,
to the set containing the values, *0* and *1*. Although these values
are written as if they were small natural numbers, you must think of
them as elements of a different type. They aren't natural numbers but
simply the two values in this other, Boolean, algebra. We could use
different symbols to represent these values. In fact, they are often
written instead as *false* (for *0*) and *true* (for *1*).The exact
symbols we use to represent these values don't really matter. What
really makes Boolean algebra what it is are the *operators* defined
by Boolean algebra and how they behave.

An algebra, again, is a set of values of a particular kind and a set
of operators involving that kind of value. Having introduced the set
of two values of the Boolean type, let's turn to the *operations* of
Boolean algebra.

Nullary, Unary, Binary, and n-Ary Operators
-------------------------------------------

The operations of an algebra take zero or more values and return (or
reduce to) values of the same kind. Boolean operators, for example,
take zero or more Boolean values and reduce to Boolean values. An
operator that takes no values (and nevertheless returns a value, as
all operators do) is called a *constant*. Each value in the value set
of an algebra can be though of as an operator that takes no values.

Such an operator is also called *nullary*. An operator that takes one
value is called *unary*; one that takes two, *binary*, and in general,
one that takes *n* arguments is called *n-ary* (pronounced "EN-airy").

Having already introduced the constant (*nullary*) values of Boolean
algebra, each of the type we have called *bool*, we now introduce the
types and behaviors the unary and binary Boolean operators, including
each of those supported in Dafny.

The Unary Operators of Boolean Algebra
--------------------------------------

While there are two constants in Boolean algebra, each of type *bool*,
there are four unary operators, each of type :math:`bool \rightarrow
bool`. This type, which contains an arrow, is a *function* type. It is
the type of any function that first takes an argument of type *bool*
then reduces to a value of type *bool*. It's easier to read, write,
and say in math than in English. In math, the type would be prounced
as "bool to bool."

There is more than one value of this function type. For example one
such function takes any *bool* argument and always returns the other
one. This function is of type "bool to bool", but it is not the same
as the function that takes any bool argument and always returns the
same value that it got. The type of each function is :math:`bool
\rightarrow bool`, but the function *values* are different.

In the programming field, the type of a function is given when it
name, its arguments, and return values are declared. This part of a
function definition is sometimes called the function *signature*, but
it's just as well to think of it as decaring the function *type*.  The
*body* of the function, usually a sequence of commands enclosed in
curly braces, describes its actual behavior, the particular function
value associated with the given function name and type.

We know that there is more than one unary Boolean function. So how
many are there? To specify the behavior of an operator completely, we
have to define what result it returns for each possible combination of
its argument values. A unary operator takes only one argument (of the
given type). In Boolean algebra, a unary function can thus take one of
only two possible values; and it can return only one of two possible
result values. The answer to the question is just the number of ways
that a function can *map* two argument values to two result values.

And the answer to this question is *four*. A function can map both *0*
and *1* to *0*; both *0* and *1* to *1*; *0* to *0* and *1* to *1*;
and *0* to *1* and *1* to *0*. There are no other possibilities. An
easy-to-understand way to graphically represent the behavior of each
of these operations is with a *truth table*.

The rows of a truth table depict all possible combinations of argument
values in the columns to the left, and in the last column on the right
a truth tables presents the corresponding resulting value.  The column
headers give names to the argument values and results column headers
present expressions using mathematical logic notations that represent
how the resulting values are computed.

Constant False
^^^^^^^^^^^^^^

Here then is a truth table for what we will call the *constant_false*
operator, which takes a Boolean argument, either *true* or *false*,
and always returns *false.* In our truth tables, we use the symbols,
*true* and *false*, instead of *1* and *0*, for consistency with the
symbols that most programming languages, including Dafny, use for the
Boolean constants. 

.. csv-table::
   :file: bool_false.csv
   :header-rows: 1
   :widths: 6, 6

Constant True
^^^^^^^^^^^^^

The *constant_true* operator always returns *true*.

.. csv-table::
   :file: bool_true.csv
   :header-rows: 1
   :widths: 6, 6
	    
Identity Function(s)
^^^^^^^^^^^^^^^^^^^^

The Boolean *identity* function takes one Boolean value as an argument
and returns that value, whichever it was. 

.. csv-table::
   :file: bool_id.csv
   :header-rows: 1
   :widths: 6, 6

As an aside we will note that *identity functions* taking any type of
value are functions that always return exactly the value they took as
an argument. What we want to say is that "for any type, *T*, and any
value, *t* of that type, the identity function for type *T* applied to
*t* always returns *t* itself. In mathematical logical notation,
:math:`\forall T: Type, \forall t: T, id_T(t) = t.` It's clearer in
mathematical language than in English! Make sure that both make sense
to you now. That is the end of our aside. Now back to Boolean algebra.

Negation
^^^^^^^^

The Boolean negation, or *not*, operator, is the last of the four
unary operators on Boolean values. It returns the value that it was
*not* given as an argument. If given *true*, it evaluates to *false*,
and if given *false*, to *true.*

The truth table makes this behavior clear.  It also introduces the
standard notation in mathematical logic for the negation operator,
:math:`\neg P`. This expression is pronounced, *not P*. It evaluates
to *true* if *P* is false, and to *false* if *P* is *true*.

.. csv-table::
   :file: bool_not.csv
   :header-rows: 1
   :widths: 6, 6

Binary Boolean Operators
------------------------

Now let's consider the binary operators of Boolean algebra. Each takes
two Boolean arguments and returns a Boolean value as a result. The
type of each such function is written :math:`bool \rightarrow bool
\rightarrow bool`, pronounced "bool to bool to bool." A truth table
for a binary Boolean operator will have two columns for arguments, and
one on the right for the result of applying the operator being defined
to the argument values in the left two columns.

Because binary Boolean operators take two arguments, each with two
possible values, there is a total of four possible combinations of
argument values: *true* and *true*, *true* and *false*, *false* and
*true*, and *false* and *false*. A truth table for a binary operator
will thus have four rows.

The rightmost column of a truth table for an operator is really where
the action is. It defines what result is returned for each combination
of argument values. In a table with four rows, there will be four
cells to fill in the final column. In a Boolean algebra there are two
ways to fill each cell. And there are exactly *12^4 = 6* ways to do
that. We can write them as *0000, 0001, 0010, 0011, 0100, 0101, 0110,
0111, 1000, 1001, 1010, 1011, 1100, 1101, 1110, 1111*. There are thus
exactly *16* total binary operators in Boolean algebra.

Mathematicians have given names to all *16*, but in practice we tend
to use just a few of them. They are called *and*, *or*, and *not*. The
rest can be expressed as combinations these operators.  It is common
in computer science also to use binary operations called *nand* (for
*not and*), *xor* (for *exclusive or*) and *implies*.  Here we present
truth tables for each of the binary Boolean operators in Dafny.


And (conjunction)
^^^^^^^^^^^^^^^^^

The *and* operator in Boolean algebra takes two Boolean arguments and
returns *true* when both arguments are *true*, and otherwise, *false*.

.. csv-table::
   :file: bool_and.csv
   :header-rows: 1
   :widths: 6, 6, 6

Nand (not and)
^^^^^^^^^^^^^^

The *nand* operator, short for *not and*, returns the opposite value
from the *and* operator: *false* if both arguments are *true* and
*true* otherwise. 

.. csv-table::
   :file: bool_nand.csv
   :header-rows: 1
   :widths: 6, 6, 6

As an aside, the *nand* operator is especially important for designers
of digital logic circuits. The reason is that *every* binary Boolean
operator can be simulated by composing *nand* operations in certain
patterns. So if we have a billion tiny *nand* circuits (each with two
electrical inputs and an output that is off only when both inputs are
on), then all we have to do is connect all these little ciruits up in
the right patterns to implement very complex Boolean functions. The
capability to etch billions of tiny *nand* circuits in silicon and to
connect them in complex ways is the heart of the computer revolution.
Now back to Boolean algebra.


Or (disjunction)
^^^^^^^^^^^^^^^^

The *or*, or *disjunction*, operator evaluates to *false* only if both
arguments are *false*, and otherwise to *true*.

It's important to note that it evaluates to *true* if either one or
both of its arguments are true. When a dad says to his child, "You can
have a candy bar *or* a donut, *he likely doesn't mean *or* in the
sense of *disjunction*.  Otherwise the child well educated in logic
would surely say, "Thank you, Dad, I'll greatly enjoy having both."

.. csv-table::
   :file: bool_or.csv
   :header-rows: 1
   :widths: 6, 6, 6

Xor (exclusive or)
^^^^^^^^^^^^^^^^^^

What the dad most likely meant by *or* is what in Boolean algebra we
call *exclusive or*, written as *xor*.  It evalutes to true if either
one, but *not both*, of its arguments is true, and to false otherwise.

.. csv-table::
   :file: bool_xor.csv
   :header-rows: 1
   :widths: 6, 6, 6

Nor (not or)
^^^^^^^^^^^^

The *nor* operator returns the negation of what the *or* operator
applied to the same arguments returns: *xor(b1,b2) = not(or(b1, b2))*.
As an aside, like *nand*, the *nor* operator is *universal*, in the
sense that it can be composed to with itself in different patterns to
simulate the effects of any other binary Boolean operator.

.. csv-table::
   :file: bool_nor.csv
   :header-rows: 1
   :widths: 6, 6, 6

Implies
^^^^^^^

The *implies* operator is used to express the idea that if one
condition, a premise, is true, another one, the conclusion, must be.
So this operator returns true when both arguments are true. If the
first argument is false, this operator returns true. It returns false
only in the case where the first argument is true and the second is
not, because that violates the idea that if the first is true then the
second must be. 


.. csv-table::
   :file: bool_implies.csv
   :header-rows: 1
   :widths: 6, 6, 6

Follows
^^^^^^^

The *follows* operator reverses the sense of an implication. Rather
than being understood to say that truth of the first argument should
*lead to* the truth of the second, it says that the truth of the first
should *follow from* the truth of the second.

.. csv-table::
   :file: bool_follows.csv
   :header-rows: 1
   :widths: 6, 6, 6

There are other binary Boolean operators. They even have names, though
one rarely sees these names used in practice.

A Ternary Binary Operator
-------------------------

Finally, to emphasize the point that there are binary operations of
all arities, we introduce just one ternary Boolean operator. It takes
three Boolean arguments and returns a Boolean result. It's type is
thus ::`bool \rightarrow bool \rightarrow bool \rightarrow bool`. We
will call it *ifThenElse_{bool}*.  The way it works is that the value
of the first argument determines which of the next two arguments
values the function returns. If the first argument is *true* then it
returns the second argument, otherwise it returns the third. So, for
example, *ifThenElse_{bool}(true, true, false)* returns true.

It is sometimes helpful to break up the name of such a function into
parts (if, then, and else( and to spread out the arguments between the
parts. So *ifThenElse_{bool}(true, true, false)* could be written as
*if true then true else false.* The link to conditional expressions
and commands in everyday programming should clear.

As an exercise for the reader: How many ternary Boolean operations are
there? Hint: an operator with *n* Boolean arguments has :math:`2^n`
possible combinations of input values. This means that there will be
:math:`2^n` rows in its truth table, and so :math:`2^n` blanks to fill
in with Boolean values in the right column. How many ways are there to
fill in :math:`2^n` Boolean values?




Languages for Symbolic Reasoning: Syntax
=====================================================================

Mathematical logic is grounded in the definition of valid sentences in
formal languages and the definition of rules for transforming one such
sentence into another in a valid way. For example, *2 + 2* is a valid
expression in the languages of arithmetic (but *2 2 + +* isn't), and
the rules of mathematical logic allow this expression to be replaced
with the expression, *4*, but not by *5*.

Why would anyone care about precisely defined transformations between
expressions in abstract languages? Well, it turns out that *syntactic*
reasoning is pretty useful. The idea is that we represent a real-world
phenomenon symbolically, in such a language, so the abstract sentence
means something in the real world.

Now comes the key idea: if we imbue mathematical expressions with
real-world meanings and then transform these expression in accordance
with valid rules for acceptable transformations of such expressions,
then the resulting expressions will also be meaningful.

A logic, then, is basically a formal language, one that defines a set
of well formed expressions, and that provides a set of *inference*
rules for taking a set of expressions as premises and deriving another
one as a consequence. Mathematical logic allows us to replace human
mental reasoning with the mechanical *transformation of symbolic
expressions*. 

To define a logic, we only have to say how to form valid expressions,
and what the rules are for transforming such expression in valid ways.
To use such a logic for practical good, which is the ultimate aim, of
course, we have to learn the art of figuring out how to represent the
real-world phenomena of interest into symbolic forms in ways that will
allow us then to use the available transformation rules repeatedly to
deduce a new expression, one that holds the answer to the question we
asked, or the result we need to act upon to have some desired effect
in and on the world.

Boolean Algebra, Expressions, and Decision Problems
===================================================

The rest of this section illustrates and further develops these ideas,
using Boolean algebra and the structure and evaluations of a language
of Boolean expressions, as a first case study in precise definition of
the syntax (sentence structure) and semantics (evaluation) of a simple
formal language: that of Boolean expressions including variables.

To illustrate the potential utility of this language and its semantics
we will define three closely related *decision problems*, show how they
can be solved in Dafny, and discuss how they lead directly to the most
important unsolved problem in the theory of computation.

The all three decision problems start with a Boolean expression, one
that can contain variables, and they ask where there is any way to
assign *true* and *false* values to the variables to make the overall
expression evaluate to *true*. The first asks whether the expression
is *satisfiable*? That is, is there at least one binding of variables
to values that makes the expression (evaluate to) *true*. The asks
whether the expression is *valid*. Does every combination of variable
values make the expression true. Last, is it *unsatisfiable*? Is it
the case that *no* combination of variable values makes the expression
true.

The problem of deciding *efficiently* whether there is a combination
of Boolean variable values that makes any given Boolean expression
true is the most important unsolved problem in computer science. We
currently do not know of a solution that with runtime complexity that
is better than exponential the number of variables in an expression.
It's easy to determine whether an assignment of values to variables
does the trick: just evaluate the expression with those values for the
variables. But *finding* such a combination today requires, for the
hardest of these problems, trying all :math:``2^n`` combinations of
Boolean values for *n* variables.

At the same time, we do not know that there is *not* a more efficient
algorithm. Many experts would bet that there isn't one, but until we
know for sure, there is a tantalizing possibility that someone someday
will find an *efficient decision procedure* for Boolean satisfiability.

Here's an example. Suppose you're given the Boolean expression,
:math:`(P \lor Q) \land (\lnot R)`. The top-level operator is
*and*. The whole expression thus evaluates to *true* if and only if
both subexpressions do. The first, :math:`(P \lor Q)`, evaluates to
*true* if either or both of *P* or *Q* do. The second evaluates to
true if and only if *R* is false. If this is the case, then there are
three ways to make the left side true, making the whole expression
true: set *P true* and *Q false*; set *P false* and *Q true*; and set
both to *true*.

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

The Syntax of Boolean Expressions
---------------------------------

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

Interpretations in Boolean Logic
--------------------------------

Given a Boolean expression with variables, an *interpretation* for
that expression is a binding of the variables in that expression to
corresponding Boolean values. A Boolean expression with no variables
is like a proposition: it is true or false on its own. An expression
with one or more variables will be true or false depending on how the
variables are used in the expression.

To make this idea precise, we will present a Dafny function that
when given a Boolean expression in our little language returns the
set of variables that appear in that expression.





A particularly important concept is that of the set of all possible
interpretations for a given Boolean expression: i.e., all the ways in
which values can be assigned to the variables in the expression. An
expression has *n* variables has :math:`2^n` interpretations.

To see that the number of interpretations is exponential in the number
of variables in an expression, consider that there are two values for
the first variable. For each of those two, there are two values for
the second variable, for a total of four interpretations for just two
variables. For each of those four, there are two possible values of a
third variable, so eight interpretations for three variables; and so
forth. Each time one adds one more variable, one *doubles* the number
of interpretations. This is a class example of exponential growth.
    

The Semantics of Boolean Expressions
------------------------------------


Evaluate a Boolean expression in a given environment.  The recursive
structure of this algorithm reflects the inductive structure of the
expressions we've defined.

.. code-block:: dafny

    type interp = map<Bvar, bool>


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

Interpretations
---------------

Validity, Satisfiability, Unsatisfiability
==========================================

