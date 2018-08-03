inductive bar : Type
| p : bar
| q : bar
open bar

#check bar
#check p

namespace inner

inductive bar : Type
| p : bar
| q : bar

#check bar -- bar here refers to foo.bar (AAA)
theorem t1 : bar = inner.bar := rfl
#check p -- as expected, p still refers to _root_.bar.p
theorem t2 : p = _root_.bar.p := rfl

open bar -- bar here refers to _root_.bar! (BBB)

#check bar -- bar still refers to foo.bar
theorem t3 : bar = foo.bar := rfl
#check p -- p still refers to _root_.bar.p
theorem t4 : p = _root_.bar.p := rfl

open foo.bar -- need to use qualified name to open namespace
#check bar -- bar still refers to foo.bar
theorem t5 : bar = foo.bar := rfl
--#check p     -- p is now ambiguous (CCC)
--theorem t6 : p = _root_.bar.p := rfl    -- p is ambiguous (DDD)

def id(a: bar): bar := a

#check id p -- but in this expression, p is not ambiguous (EEE)

end foo