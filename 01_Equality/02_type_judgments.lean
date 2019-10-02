/- * Type judgments * -/

/-
Recall the inference rule for Leibniz equality.

  T: Type, t : T
  -------------- (eq.refl)
     pf: t = t

Above the line in this inference rule, we meet a 
new kind of judgment here: a type judgment. If X 
is some type (such as string, bool, or nat), and 
x is a value of that type, X, we can denote this 
fact by writing x : X. We read this as "x is of 
type X."

The Lean tool, which you're using, is based on a
foundational theory called type theory. In type
theory, every object (value) and every expression 
has a type. Every parameter, such as an argument 
to a function, has a type, as does the value that
a function returns. Every well formed expression 
has a unique type. 

In Lean you can check the type of an expression
by using the #check command. 
-/

#check 0
#check "Hi!"
#check tt

/-
Note that ℕ is math shorthand for the type of 
natural numbers, i.e., non-negative integers 
(thus zero on up). Hover your mouse over the 
#check commands to see what are the types of 0,
"Hi!", and tt in Lean.
-/

/-
Now here's an amazing idea. In Lean, types are 
values, too! It thus follows that a type must 
have a type. So what is the type of a type? Well,
let's check a few!
-/

#check nat
#check bool
#check string

/-
Partial answer: The type of any ordinary data
type is simply "Type".

Now the curious and insightful student will ask,
"Well, then, what about Type, itself? Is it a value?
What is its type?"
-/

#check Type
#check Type 1
#check Type 2
-- etc!

/-
So, if T is some data type, then we'd write the
type  judgment, "T : Type". And if T is a type, 
and t a value of type, T, then we'd write t : T. 
-/

/-
With all that out of the way, we can once again 
write and now more fully understand the inference 
rule for equality that we really want. 

T: Type, t : T
-------------- (eq.refl)
  pf: t = t

Those are now type judgments above the line. You can 
understand this inference rule as saying this: "if you 
give me a T that is a type (e.g., bool, nat, string), 
and if you also give me a value, t, of that type, T, 
(e.g., 0 or true), I will give you back a proof that 
t = t. 

This single inference rule thus defines a very sensible notion of equality for all values of all types that now
exist or might ever be defined. 

So now, rather than a separate axiom for 0 = 0,
another one for 1 = 1, another for true = true, and
yet another for Fido = Fido, so forth, we have one 
a single inference rule that derives them all as
special cases, one case for every possible value,
and type of, t.

You can think of the "inputs" above the line as 
parameters. That is how we generalize from a single
case to an infinity of cases.

/- * Inference rules as computations * -/

Indeed, you can now start to think of eq.refl in
two different ways: as a logical inference rule,
and as a kind of program! This program takes two
arguments. The first is a type and the second is 
a value of the type given as the first argument.
The program then returns a proof that the second
argument is equal to itself. 

We are given this inference rule as something 
akin to an axiom, in the sense that it does not
require proofs of other propositions as arguments.
The only "proofs" it requires as inputs are proofs 
that T is a type and t is a value of that type. 
That is, its inputs are not proofs of proposition,
but rather are type judgments. 

EXERCISE: Take the view that eq.refl is a program
that takes two parameters as discussed here, and
write an expression that reduces to ("returns") a 
proof of the proposition that the natural number, 
0, is equal to itself. 

EXERCISE: Give comparable expressions that return
proofs of equality-with-self for the Boolean value, 
tt, and for the string value, "Hello Lean".
-/
