Logical Specifications, Imperative Implementations
==================================================

We've discussed requirements, specifications, and implementations as
distinct artifacts that serve distinct purposes. For good reasons,
these artifacts are usually written in different languages. Software
implementations are usually written in programming languages, and, in
particular, are usually written in *imperative* programming languages.
Requirements and specifications, on the other hand, are written either
in natural language, e.g., English, or in the language of mathematical
logic. 

This unit discusses these different kinds of languages, why they are
used for different purposes, the advantages and disadvantages of each,
and why modern software development requires fluency in and tools for
handling artifacts written in multiple such languages. In particular,
the educated computer scientist and the capable software developer
must be fluent in the language of mathematical logic.

Imperative Languages for Implementations
----------------------------------------

The language of implementations is code, usually written in what we
call an *imperative* programming language. Examples of such languages
include Python, Java, C++, and Javascript.

The essential property of an imperative language is that it is
*procedural*. Programs in these languages describe step-by-step
*procedures*, in the form of sequences of *commands*, for solving
given problem instances. Commands in turn operate (1) by reading,
computing with, and updating values stored in a *memory*, and (2) by
interacting with the world outside of the computer by executing input
and output (I/O) commands.

Input (or *read*) commands obtain data from *sensors.* Sensors include
mundane devices such as computer mice, trackpads, and keyboards. They
also include sensors for temperature, magnetism, vibration, chemicals,
biological agents, radiation, and face and license plate recognition,
and much more. Sensors convert physical phenomena in the world into
digital data that programs can manipulate. Computer programs can thus be
made to *compute about reality beyond the computing machine*.

Output (or *write*) commands turn data back into physical phenomena in
the world. The cruise control computer in a car is a good example.  It
periodically senses both the actual speed of the car and the desired
speed set by the driver. It then computes the difference and finally
finally it outputs data representing that difference to an *actuator*
that changes the physical accelerator and transmission settings of the
car to speed it up or slow it down. Computer programs can thus also be
made to *manipulate reality beyond the computing machine*.

A special part of the world beyond of the (core of a) computer is its
*memory*. A memory is to a computer like a diary or a notebook is to a
person: a place to *write* information at one point in time that can
then be *read* back later on. Computers use special actuators to write
data to memory, and special sensors to read it back from memory when
it is needed later on. Memory devices include *random access memory*
(RAM), *flash memory*, *hard drives*, *magnetic tapes*, *compact* and
*bluray* disks, cloud-based data storage systems such as Amazon's *S3*
and *Glacier* services, and so forth.

Sequential progams describe sequences of actions involving reading of
data from sensors (including from memory devices), computing with this
data, and writing resulting data out to actuators (to memory devices,
display screens, and physical systems controllers). Consider the
simple assignment command, *x := x + 1*. It tells the computer to
first *read* in the value stored in the part of memory designated by
the variable, *x, to add one to that value, and finally to *write* the
result back out to the same location in memory. It's as if the person
read a number from a notebook, computed a new number, and then erased
the original number and replaced it with the new number. The concept
of an updateable memory is at the very heart of the imperative model
of computation.

Declarative Languages for Specifications
----------------------------------------

The language of formal requirements and specifications, on the other
hand, is not imperative code but *declarative* logic.  Expressions in
such logic will state *what* properties or relationships must hold in
given situation without providing a procedures that describes *how*
such results are to be obtained. 

.. Examples of
.. logics that we will study and use include *propositional* and
.. *predicate* logic.  An example of a kind of logic important in
.. software development but that we will not study in this class is
.. *temporal logic.*
.. For purposes of software specification, the most salient property of
.. such a logical language is that it is *declarative*.  

To make the difference between procedural and declarative styles of
description clear, consider the problem of computing the positive
square root of any given non-negative number, *x*. We can *specify*
the result we seek in a clear and precise logical style by saying
that, for any given non-negative number *x*, we require a value, *y*,
such that :math:`y^2 = x`. Such a *y*, squared, gives *x*, and this
makes *y* a square root.

We would write this mathematically as :math:`\forall x \in {\mathbb R}
\mid x >= 0, y \in {\mathbb R} | y^2 >= 0 \land y^2 = x`. In English,
we'd pronounce this expression as, "for any value, *x*, in the real
numbers, where *x* is greater than or equal to zero, the result is a
value, *y*, also in the real numbers,, where *y* is greater than or
equal to zero and *y* squared is equal to *x*." (The word, *where*,
here is also often pronounced as *such that*. Repeat it to yourself
both ways until it feels natural to translate the math into spoken
English.)

Let's look at this expression with care. First, the symbol,
:math:`\forall`, is read as *for all* or *for any*. Second, the symbol
:math:`{\mathbb R}`, is used in mathematical writing to denote the set
of the *real numbers*, which includes the *integers* (whole numbers,
such as *-1*, *0*, and *2*), the rational numbers (such as :math:`2/3`
and *1.5*), and the irrational numbers (such as *pi* and *e*). The
symbol, :math:`\in`, pronounced as *in*, represents membership of a
value, here *x*, in a given set. The expression, :math:`\forall x \in
{\mathbb R}` thus means "for any value, *x*, in the real numbers," or
just "for any real number, *x*".

The vertical bar followed by the statement of the property, *x >= 0*,
restricts the value being considered to one that satisfies the stated
property. Here the value of *x* is restricted to being greater than or
equal to zero. The formula including this constraint can thus be read
as "for any non-negative real number, *x*." The set of non-negative
real numbers is thus selected as the *domain* of the function that we
are specifying.


The comma is our formula is a major break-point. It separates the
specification of the *domain* of the function from a formula, after
the comma, that specifies what value, if any, is associated with each
value in the domain.  You can think of the formula after the comma as
the *body* of the function. Here it says, assuming that *x* is any
non-negative real numner, that the associated value, sometimes called
the *image* of *x* under the function, is a value, *y*, also in the
real numbers (the *co-domain* of the function), such that *y* is both
greater than or equal to zero equal *and* :math:`y^2 = x`. The symbol,
:math:`\land` is the logical symbol for *conjunction*, which is the
operation that composes two smaller propositions or properties into a
larger one that is true or satisfied if and only if both constituent
propositions or properties are. The formula to the right of the comma
thus picks out exactly the positive (or more accurate a non-negative)
square root of *x*.

We thus have a precise specification of the positive square root
function for non-negative real numbers. It is defined for every value
in the domain insofar as every non-negative real number has a positive
square root. It is also a *function* in that there is *at most one*
value for any given argument. If we had left out the non-negativity
*constraint* on *y* then for every *x* (except *0*) there would be
*two* square roots, one positive and one negative. We would then no
longer have a *function*, but rather a *relation*. A function must be
*single-valued*, with at most one "result" for any given "argument".

We now have a *declarative specification* of the desired relationship
between *x* and *y*. The definition is clear (once you understand the
notation), it's concise, it's precise. Unfortunately, it isn't what we
call *effective*. It doesn't give us a way to actually *compute* the
value of the square root of any *x*. You can't run a specification in
the language of mathematical logic (at least not in a practical way).


Refining Declarative Specifications into Imperative Implementations
-------------------------------------------------------------------

The solution is to *refine* our declarative specification, written in
the language of mathematical logic, into a computer program, written
in an imperative language: one that computes *exactly* the function we
have specified. To refine means to add detail while also preserving
the essential properties of the original. The details to be added are
the procedural steps required to compute the function. The essence to
be preserved is the value of the function at each point in its domain.

In short, we need a step-by-step procedure, in an imperative language,
that, when *evaluated with a given actual parameter value*, computes
exactly the specified value. Here's a program that *almost* does the
trick. Written in the imperative language, Python, it uses Newton's
method to compute *floating point* approximations of positive square
roots of given non-negative *floating point* arguments.

.. code-block:: python

   def sqrt(x):
       """for x>=0, return non-negative y such that y^2 = x"""
       estimate = x/2.0
       while True:
           newestimate = ((estimate+(x/estimate))/2.0)
           if newestimate == estimate:
               break
           estimate = newestimate
       return estimate

This procedure initializes and then repeatedly updates the values
stored at two locations in memory, referred to by the two variables,
*estimate* and *newestimate*. It repeats the update process until the
process *converges* on the answer, which occurs when the values of the
two variables become equal. The answer is then returned to the caller
of this procedure.

Note that, following good programming style, we included an English
rendering of the specification as a document string in the second line
of the program.  There are however several problems using English or
other natural language comments to document specifications. First,
natural language is prone to ambiguity, inconsistency, imprecision,
and incompleteness. Second, because the document string is just a
comment, there's no way for the compiler to check consistency between
the code and this specification. Third, in practice, code evolves (is
changed over time), and developers often forget, or neglect, to update
comments, so, even if an implementation is initially consistent with a
such a comment, inconsistencies can and often do develop over time.

In this case there is, in fact, a real, potentially catastrophic,
mathematical inconsistency between the specification and what the
program computes. The problem is that in Python, as in many everyday
programming languages, so-called *real* numbers are not exactly the
same as the real (*mathematical*) reals!

You can easily see what the problem is by using our procedure to
compute the square root of 2.0 and by then multiplying that number by
itself. The result of the computation is the number *1.41421356237*,
which we already know has to be wrong to some degree, as the square
root of two is an *irrational* number that cannot be represented by
any non-terminating, non-repeating decimal. Indeed, if we multiply
this number by itself, we get the number, *1.99999999999*. We end up
in a situation in which *sqrt(2.0) \* sqrt(2.0)* isn't equal to 2.0!

The problem is that in Python, as in most industrial programming
languages, *so-called* real numbers (often called *floating point*
numbers) are represented in just 64 binary digits, and that permits
only a finite number of digits after the decimal to be represented.
And additional *low-order* bits are simply dropped, leading to what
we call *floating-point roundoff errors.* That's what we're seeing
here.

In fact, there are problems not only with irrational numbers but with
rational numbers with repeating decimal expansions when represented in
the binary notation of the IEEE-754 (2008) standard for floating point
arithmetic. Try adding *1/10* to itself *10* times in Python. You will
be surprised by the result. *1/10* is rational but its decimal form is
repeating in base-2 arithmetic, so there's no way to represent *1/10*
precisely as a floating point number in Python, Java, or in many other
such languages.

There are two possible solutions to this problem. First, we could
change the specification to require only that *y* squared be very
close to *x* (within some specified margin of error). The we could
show that the code satisfies this approximate definition of square
root. An alternative would be to restrict our programming language to
represent real numbers as rational numbers, use arbitrarily large
integer values for numerators and denominators, and avoid defining any
functions that produce irrational values as results. We'd represent
*1/10* not as a 64-bit floating point number, for example, but simply
as the pair of integers *(1,10)*. 

This is the solution that Dafny uses.  So-called real numbers in Dafny
behave not like *finite-precision floating point numbers that are only
approximate* in general, but like the *mathematical* real numbers they
represent. The limitation is that not all reals can be represented (as
values of the *real* type in Dafny. In particular, irrational numbers
cannot be represented exactly as real numbers. (Of course they can't
be represented exactly by IEEE-754 floating point numbers, either.) If
you want to learn (a lot) more about floating point, or so-called
*real*, numbers in most programming languages, read the paper by David
Goldberg entitled, *What Every Computer Scientist Should Know About
Floating-Point Arithmetic.* It was published in the March, 1991 issue
of Computing Surveys. You can find it online.


Why Not a Single Language for Programming and Specification?
------------------------------------------------------------

The dichotomy between specification logic and implementation code
raises an important question? Why not just design a single language
that's good for both?

The answer is that there are fundamental tradeoffs in language design.
One of the most important is a tradeoff between *expressiveness*, on
one hand, and *efficient execution*, on the other.

What we see in our square root example is that mathematical logic is
highly *expressive*. Logic language can be used so say clearly *what*
we want. On the other hand, it's hard using logic to say *how* to get
it. In practice, mathematical logic is clear but can't be *run* with
the efficiency required in practice.

On the other hand, imperative code states *how* a computation is to be
carried out, but generally doesn't make clear *what* it computes. One
would be hard-pressed, based on a quick look at the Python code above,
for example, to explain *what* it does (but for the comment, which is
really not part of the code). 

We end up having to express *what* we want and *how* to get it in two
different languages. This situation creates a difficult new problem:
to verify that a program written in an imperative language satisfies,
or *refines*, a specification written in a declarative language.  How
do we know, *for sure*, that a program computes exactly the function
specified in mathematical logic?

This is the problem of program *verification*. We can *test* a program
to see if it produces the specified outputs for *some* elements of the
input domain, but in general it's infeasible to test *all* inputs. So
how can we know that we have *built a program* right, where right is
defined precisely by a formal (mathematical logic) specification) that
requires that a program work correctly for all (:math:`\forall`) inputs?

