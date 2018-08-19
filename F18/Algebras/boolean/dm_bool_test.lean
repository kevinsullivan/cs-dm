/-
To use definitions from another lean, you must
"import" that file: directly or indirectly. If
you don't import, then the symbols in that file
are not defined in this one. To see, uncomment 
the following line. Hover to see the error and
understand what it's saying.

As an aside, importing from a file reveals the
definitions at the top-level namespace. If some
sumbols in that file are defined in namespaces,
then either the names in the file must qualified,
or the namespace has to be opened.
-/

-- #check dm_bool

/-
To use definitions established in another .lean file,
"import" the file by name. 

Lean has to know where to look to find the file. It 
has several ways to do this. We use a simple one: we 
prefix the file name with a dot (period) to tell lean 
to look for the current directory, the same directory
as this file (dm_bool_test.lean). 
-/

import .dm_bool


/-
Having imported from that file, you can now use the 
definitions from there, provided you use qualified
names. As an example, the type, dm_bool, is defined
in dm_bool.lean, and within the  edu.virginia.cs.dm
namespace.
-/

#check edu.virginia.cs.dm.dm_bool

/-
If you want to use identifiers defined from that
file without explicit qualification, you have to 
"open" the namespace.
-/

open edu.virginia.cs.dm

/-
Having imported from dm_bool.lean and 
opened the edu.virginia.cs.dm namespace,
we can now access definitons from that 
file without the namespace qualifiers.
-/

#check dm_bool

/-
That's what you go through when you want 
the module you're writing (in this file) 
to be able to use definitions from another 
module (another file) without qualifiers.
-/

/-
You may still need to use qualifiers to 
access definitions from that module that
are nested inside other namespaces. Here
is an example.
-/

-- #check dm_tt /- doesn't work -/

#check dm_bool.dm_tt

-- open dm_bool /- doesn't work! explain. -/

/-
We can now use the dm_bool type in this 
mofule. file. We'll also want to use the
functions that implement the operators
defined in that file.
-/

#check and_boolean

/-
we are now set up to write test cases for
the dm_bool-related code in that module.
-/

/-
A test case is a little program and two 
values: the value expected according to
this test case, and the value actually 
obtained when the program is run.

Here's an example. We understand the
following program to be an expression
that reduces to the conjuection of the
Boolean true and false values, which 
is false. That's the expected value.
Now hover over the #check to see the
answer actually obtained by "running.
(evaluating) the program.
-/

#reduce and_boolean 
            dm_bool.dm_tt
            dm_bool.dm_ff

/-
The actual result equals the expeced
result. So we say that the program 
passed the test (case).
-/

/-
All that this this means, however is 
that "the test case did not succeed in 
flagging a possible programming bug."
So in a sense a test case the a program
passes is a failure.
-/

/-
Testing succeeds when it finds important
bugs in your program: bugs that you didn't
know about and that you would think need
to be fixed. 
-/

/-
EXERCISE: WRITE A BUNCH OF TEST CASES
-/