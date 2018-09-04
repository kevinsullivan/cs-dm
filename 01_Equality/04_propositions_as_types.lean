/-
Wait! Lean is telling us that: eq.refl 0 : 0 = 0.
Putting parenthesis in can make it easier to read:
(eq.refl 0) : (0 = 0). We've so far read this as 
saying that (eq.refl 0) is a proof of 0 = 0. But 
the observant reader will see that it looks just 
like a type judgment as well. It looks like it's 
saying that (eq.refl 0) is a value of type (0 = 0).

And indeed that is exactly what it's saying. Here
is the deep idea: in the "constructive logic" of 
Lean, propositions are formalized as types, and 
proofs are represented values of these types! 

A proof, then, is valid for a given proposition
if it is a value of the corresponding type. And
Lean's type checker can always determine whether 
that is the case! In lieu of human checking of
the validity of proofs, we therefore now have a 
mechanical proof checker!

Read the eq.refl inference rule again. We can 
now see it clearly as defining a computation. 
It can now be seen as saying, "if you give me 
any value, t, I will infer its type, T, and will 
construct and return a value of type, t = t. 
Not only that but the type-checker will provide 
you with a very high degree of assurance that 
it's a valid proof! 
-/

/-
We can also now understand what it means when we
say that Lean is a proof checker. It means that
Lean will not allow us to use proofs that are not
valid with respect to the propositions/types they 
are said to prove, because they won't type check.
-/

/-
Let's look at type checking a little more deeply.
We can always assign to a variable a value of the 
type that the variable is declared to have. 
-/

def n : nat := 1

/-
This Lean definition says that n is a variable 
for which a value of type nat must be provided
(n : nat), and it goes on to assign to n ( := )
the value 1. 
  
The Lean type checker checks that 1 is a
value of type nat, which it is. Lean therefore
accepts the definition, and consequently n is 
defined, with the value, 1, for the remainder 
of this file.
-/

/-
EXERCISE: Define s to have the type, string,
and the value, "Hello, Lean!"
-/

/-
We note that we could have elided the explicit
type declaration (n : nat), as Lean infers from 
the value, 1, on the right, that the intended 
type of n can only be nat.
-/

def n' := 1
#check n'

/-
EXERCISE: define s' to be "Hello, Lean", leaving
it to Lean to infer the type of s'.
-/

/-
The type checker also absolutely prevents the
assignment to a variable of a value that is not
of the right type. Read the following code and
identify the type error, then uncomment it and
see how Lean detects and reports the error. Be
sure you understand the error message. This one
is self-explanatory.
-/

-- def n'' : nat := "Hello Lean!"

/-
Now let's replace the "nat" type with the
type "0 = 0." Remember, every proposition is
now viewed as a type. We could thus similarly
declare a variable, p, to have this type, just
as we declared n to have type nat. Finally we
would need to assign to p a value of this type,
which is to say a proof of 0 = 0. Compare this 
code carefully with that for n, above. Note 
the deep parallels. Here, however, rather than
assigning a value such as 1, we're assigning 
a value that is a proof, and it, in turn, is
produced by applying the eq.refl inference
rule to the value 0.
-/

def      p     :  0 = 0   :=   (eq.refl 0)
/-    variable    type    bind  value/proof   
-/

#check p    -- what is the type of p?
#reduce p   -- what is the value of p?

/-
EXERCISE: To the variable s, bind a proof of
the proposition that "Hello Lean!" is equal 
to itself.

EXERCISE: Do the same for the Boolean value,
tt.
-/

/-
And just as the type checker prevents the
assignment of a value that is not of the
right type to a variable such as n, so it
also prevents the assignment to p of a
proof that is not of the right type. 
-/

/-
EXERCISE. Explain precisely why Lean 
reports an error for this code and what
it means. (Uncomment the code to see the
error, then replace the comments so that
the error isn't a problem in the rest of
this file.)
-/

-- def p' : 0 = 0 := (eq.refl 1)

/-
EXERCISE: Explain why could you never use
eq.refl to successfully produce a proof
of 0 = 1? Explain.
-/

/-
In Lean and related proof assistants,
propositions are types, proofs are values
of proposition types, and proof checking 
*is* type checking. Put a start next to
this paragraph and be sure that you
understand it. It takes time and study
to fully grasp these concepts.
-/

/-
EXERCISE: Prove the following theorem,
teqt, that 2 = 1 + 1. Try using eq.refl.
-/

/-
That last proposition, 2 = 1 + 1, is a bit
different because it has different terms on
each side of the equals sign. In Lean, these
terms are reduced (evaluated) before they are
compared, and so eq.refl can still be used 
to prove this proposition. 
-/


/- * What is the type of a proposition? *-/

/-
We've already seen that types are values, 
too, and that a type thus has a type. The
type of nat is Type, for example. So, in 
Lean, what is the type of a proposition, 
such as 0 = 0? Let's find out using #check. 
-/

#check (0 = 0)

/-
EXERCISE: What is the type of (0 = 1)?
Answer before you #check it, then #check 
it to confirm.

EXERCISE: What is the type of "Hello Lean" =
"Hello Lean"?
-/

/-
Lean tells us that the type of each proposition is
Prop. In Lean, every logical proposition is of type
Prop, just as every ordinary computational type, such
as nat, bool, or string, is of type, Type. So how
do Prop and Type relate? Where does Prop fit in? 
What is its type? What is the type of Prop? We can 
of course just #check it!
-/

#check Prop

/-
Ah ha. Prop is of type Type, which is to say that 
that Prop is of type, Type 0. We thus now have a
complete picture of the type hierarchy of Lean.

Prop   :   Type : Type 1 : Type 2 : Type 3 : ...
  |          |
0 = 0       nat
  |          |
eq.refl 0    1

Prop is the first type in the hierarchy. Every
propositional type is of type Prop. We illustrate
here that the type (0=0) is of type Prop, but so
is 0 = 1, 1 = 1, tt = tt, and so are all of the
other propositions we'll ever see in Lean. All 
propositions, which again are themselves types,
are of type Prop in the logic of Lean.

By contrast, computational types, such as nat,
but also string, bool, and function types (we
will see them soon enough) are of type, Type.

The lowest layer in the diagram illustrates
where values fit in. The proof, eq.refl 0,
is a value of type (0 = 0), just as 1 is a
value of type nat.

We will never need types above Type in this 
class. Mathematicians, logicians, and program
verification experts who use Lean and other tools
like it do sometimes need to be careful about how
values fall into the various "type universes,"
as these various levels are called. 
-/

