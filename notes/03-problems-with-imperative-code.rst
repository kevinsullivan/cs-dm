********************************
3. Problems with Imperative Code
********************************

There's no free lunch: One can have the expressiveness of mathematical
logic, useful for specification, or one can have the ability to run
code efficiently, along with indispensable ability to interact with an
external environment provided by imperative code, but one can not have
all of this at once at once.

A few additional comments about expressiveness are in order here. When
we say that imperative programming languages are not as expressive as
mathematical logic, what we mean is not ony that the code itself is not
very explicit about what it computes. It's also that it is profoundly
hard to fully comprehend what imperative code will do when run, in large
part due precisely to the things that make imperative code efficient: in
particular to the notion of a mutable memory.

One major problem is that when code in one part of a complex program
updates a variable (the *state* of the program), another part of the
code, far removed from the first, that might not run until much later,
can read the value of that very same variable and thus be affected by
actions taken much earlier by code far away in the program text. When
programs grow to thousands or millions of lines of code (e.g., as in
the cases of the Toyota unintended acceleration accident that we read
about), it can be incredibly hard to understand just how different and
seemingly unrelated parts of a system will interact.

As a special case, one execution of a procedure can even affect later
executions of the same procedure. In pure mathematics, evaluating the
sum of two and two *always* gives four; but if a procedure written in
Python updates a *global* variable and then incoporates its value into
the result the next time the procedure is called, then the procedure
could easily return a different result each time it is called even if
the argument values are the same. The human mind is simply not powerful
enough to see what can happen when computations distant in time and in
space (in the sense of being separated in the code) interact with each
other.

A related problem occurs in imperative programs when two different
variables, say *x* and *y*, refer to the same memory location. When
such *aliasing* occurs, updating the value of *x* will also change the
value of *y*, even though no explicit assignment to *y* was made. A
piece of code that assumes that *y* doesn't change unless a change is
made explicitly might fail catastrophically under such circumstances.
Aliasing poses severe problems for both human understanding and also
machine analysis of code written in imperative languages.

Imperative code is thus potentially *unsafe* in the sense that it can
not only be very hard to fully understand what it's going to do, but
it can also have effects on the world, e.g., by producing output
directing some machine to launch a missile, fire up a nuclear reactor,
steer a commercial aircraft, etc.

