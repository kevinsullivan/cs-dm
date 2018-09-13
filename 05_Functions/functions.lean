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
prevent our using types such as nat and
bool as P and Q. In this case we'd say
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
ℕ → bool. 
-/

def zero_nat (n : ℕ) : nat := 0 -- explicit return type
#check zero_nat
#check zero_nat 5
#reduce zero_nat 5

def zero_nat': ℕ → ℕ := λ n : nat, (0 : nat)
def zero_nat'': ℕ → ℕ := λ n, 0
def zero_nat''' := λ n : nat, 0

/- 
EXERCISE: define a function, one_nat that takes any natural 
number as an argument and always returns the natural number 
1. Write it in traditional function definition notation and
using lambda expressions and type inference. 
-/

def identity_nat (n : ℕ) : nat := n --explicit return type
#check identity_nat
#check identity_nat 5
#reduce identity_nat 5

/- 
EXERCISE: define the same function, call it identity_nat'
and write it using a lambda expression.  
-/

def double (n : ℕ) := 2 * n -- return type inferred
#check double
#check double 3
#reduce double 3

/-
EXERCISE: Write it using a lambda expression.
-/

def square (n: ℕ) := n * n -- return type inferred
#check square
#check square 3
#reduce square 3

/-
EXERCISE: Write it using a lambda expression.
-/
def isPositive (n: nat) : bool := 
    if n > 0 then tt else ff

#check isPositive
#check isPositive 0
#check isPositive 1
#check isPositive 2
#reduce isPositive 0
#reduce isPositive 1
#reduce isPositive 2

/-
EXERCISE: Write it using a lambda expression.
-/

/-
Here's a function that returns boolean true
(tt) if a given natural number n is greater
than or equal to zero and less than 2^32. It
is given using lambda notation. Write it with
a prime on its name using ordinary function
definition notation (as the functions above
are written). 
-/

def uint32: ℕ → bool := 
    λ n, 
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
#check λ n, n > 0


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

/-
EXERCISE: Give two or three examples
of interesting functions from nat to
nat. A program that takes any natural
number as an argument and always returns
a natural as a result is a value
(a "function", or it would be better to
say, a lambda expression) of this type, 
ℕ → ℕ
-/


/-
We can also pass functions as arguments
to other functions!
-/

def compose (f: ℕ → ℕ) (g: ℕ → ℕ) (x: ℕ) : ℕ :=
  f (g x)

#check compose
#check compose square double
#reduce compose double double 3
#reduce compose square double 3
#reduce square (double 3)

def do_twice (f : ℕ → ℕ) (x: ℕ) : ℕ := f (f x)
#check do_twice
#reduce do_twice square 3

/-
Let's write this as a lambda expression and 
see what we get.
-/

def do_twice' : (ℕ → ℕ) → ℕ → ℕ := 
    λ f x, f (f x)

/-
And that's a shorthand for this!
-/

def do_twice'' : (ℕ → ℕ) → ℕ → ℕ := 
    λ f : (ℕ → ℕ),
        λ (x : ℕ), 
            f (f x)

theorem dt_eq_dt : do_twice = do_twice'' := rfl

/-
Inception! Here we define a function that takes
as an argument a function that takes as an argument
a function (and a natural number)
-/

def do_twice''' (f: (ℕ → ℕ) → ℕ → ℕ) (x: (ℕ → ℕ)) : (ℕ → ℕ) := f (f x)

#check do_twice'''
#check do_twice''' do_twice
#reduce do_twice'''

/-
Use #eval instead of #reduce because #reduce will
have recursion problems unless we increase our
stack space.
-/

#eval (do_twice''' do_twice) square 2
#eval 2^16
