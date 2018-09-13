/-
If P and Q are of type Prop, we think
of P → Q as a proposition in the form
of an implication. 

Moreover, as we've seen, the way that 
we give a proof of P → Q in the logic
of Lean is to produce a function that,
if given a proof of P returns a proof 
of Q.

On the other hand, nothing in Lean will 
prevent our using types such as bool and
int as P and Q. In this case we'd say
that P → Q, or nat → bool, is a type: a
type of functions from P → Q, e.g., from
nat to bool.

EXERCISE: Give two or three examples
of interesting functions from nat to
bool. A program that takes any natural
number as an argument and always returns
a Boolean value as a result is a value
(a "function", or it would be better to
say, a lambda expression) of this type, 
P → Q. 
-/

def positive (n: nat) : bool := 
    if n > 0 then tt else ff

#check positive

def uint32 (n: nat) : bool := 
    if n >= 0 ∧ n < 2^32 then tt else ff

#check uint32

/-
An equivalent function definition with
a type declaration using arrow notation, 
and an explicit lambda expression as a 
value.
-/
def positive' : nat → bool :=
    λ n : nat, 
        (if n > 0 then tt else ff : bool)

#check positive'

#check λ n : nat, (if n > 0 then tt else ff : bool)
#check λ n, (if n > 0 then tt else ff)

/-
Read the first line as saying positive'
is a proof of (a value of type) nat → bool.
There are many values of this type: they
are all the functions taking nat arguments
and returning bool results. The specific
value that we use here to "prove the type"
is the function that returns true if the
argument is strictly greater than zero,
otherwise is returns false.

Read the lambda expression as follows:
A function that takes an argument, n, of
type nat, and that returns the result of
evaluating the expression, involving n,
after the comma: here, true if n > 0,
and false otherwise.

Here's an equivalent expression using 
type inference to skip declaring the
type of n.
-/

def positive'' : nat → bool :=
    λ n, if n > 0 then tt else ff 

/-
Here we use type inference to skip
declaring the function type, while
still using a lambda expression for
the program.
-/

def positive''' := 
    λ n, if n > 0 then tt else ff 

#check positive'''
#reduce positive''' 3
#reduce positive''' 0

theorem  modus_tollens { P Q : Prop } (pfPtoQ : P → Q) (pfnQ : Q → false) : 
    ¬ P:= λ pfP, pfnQ (pfPtoQ pfP)
        
theorem qAndNotQfalse { P Q: Prop } (pf: Q ∧ ¬ Q) : false := pf.2 pf.1

theorem notQAndNotQ: ∀ Q : Prop, ¬ (Q ∧ ¬ Q) :=
    λ (Q : Prop) (qanq : Q ∧ ¬ Q), qanq.2 qanq.1

/-
theorem proof_by_contra_1 { P Q : Prop } (pfNotPImpQNotQ: ¬ P → (Q ∧ ¬ Q)) : P :=
    _

You've got nothing in the context from which to construct a proof of P. Proof by 
contradiction is not constructive and so can't be done in plain Lean, Coq, etc.
-/

