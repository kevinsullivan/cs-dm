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

import .csdm_bool

/-
Having imported the definitions from that file, you
can now use the definitions established there. (There
are ways for the developer to control which definitions
from a given file are made available by doing an import.
We'll see that detail later on.)
-/

#check csdm.bool

/-
We still have to be careful
-/