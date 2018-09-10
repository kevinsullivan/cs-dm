-- UNDER CONSTRUCTION

/-
If P and Q are of type Prop, we think
of P → Q as a proposition in the form
of an implication. 

On the other hand, nothing in Lean will 
prevent our using types such as bool and
int as P and Q, leading to functions of
type nat → bool. A program that turns any
natural number into a Boolean value is
a function of this type, and we can also
say it is a proof of P → Q. 
-/

def positive (n: nat) : bool := 
    if n > 0 then tt else ff

def positive' : nat → bool :=
    λ n : nat, (if n > 0 then tt else ff : bool)

def positive'' : nat → bool :=
    λ n, if n > 0 then tt else ff 