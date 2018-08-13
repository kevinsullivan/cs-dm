/-
If you try to use definitions established in another
lean file without "importing" those definitions, it 
will not work. Uncomment the following line and see
the error message.
-/

-- #check csdm.bool

/-
To use definitions established in another .lean file,
you have to use the "import" command in lean followed
by the name of the file. Lean has to know where to look
to find the file. It has several ways to do this. Here
we use a simple one: we prefix the name of the file
with a dot (period) to tell lean to look for the file
in the same directory as this file (csdm_bool_test). 
-/

import .dm_bool


/-
Having imported the definitions from that file, you
can now use the definitions established there. 
-/

#check edu.virginia.cs.dm.dm_bool

/-
If you want to use identifiers defined within a
namespace without explicitly typing the name of
the namespace, you have to "open" the namespace.
-/

open edu.virginia.cs.dm

#check edu.virginia.cs.dm.dm_bool

/-
Having imported dm_bool and opened the
edu.virginia.cs.dm, we are now set up to
write test cases for the dm_bool-related
code in that module.
-/

-- TBD