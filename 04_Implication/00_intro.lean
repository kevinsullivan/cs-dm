/-
Given any two propositions, P and Q, we can form
the proposition, P → Q. That is the syntax of an
implications. 

If P and Q are propositions, we read P → Q as 
P implies Q. A proof of a proposition, P → Q, 
is a program that that converts any proof of P 
into a proof of Q. The type of such a program 
is P → Q.
-/

/- Elimination Rule for Implication -/

/-
From two premises, (1) that "if it's raining then
the streets are wet," and (2) "it's raining,"" we 
can surely derive as a conclusion that the streets
are wet. Combining "raining → streets wet" with 
"raining" reduces to "streets wet." This is modus
ponens.

Let's abbreviate the proposition "it's raining", 
as R, and let's also abbreviate the proposition, 
"the streets are wet as W". We will then abbreviate
the proposition "if it's raining then the streets 
are wet" as R → W. 

Such a proposition is in the form of what we call 
an implication. It can be pronounced as "R implies 
W", or simply "if R is true then W must be true." 
Note that by this latter reading, in a case where 
R is not true, the implication says nothing about 
whether W must be true or not. We will thus judge
an implication to be true if either R is false (in
which case the implications does not constrain W
to be any value), or if whenever R is true, W is,
too. The one situation under which we will not be
able to judge R → W to be true is if it can be
the case that R is true and yet W is not, as that
would contradict the meaning of an implication. 

With these abbreviations in hand, we can write 
an informal inference rule to capture the idea
we started with. If we know that a proposition,
R → W, is true, and we know that the proposition,
R, is true, then we can deduce that W therefore 
must also be true. We can write this inference
rule informally like this: 

  R → W, R
  -------- (→ elim)
     W

This is the arrow (→) elimination rule?

In the rest of this chapter, we will formalize
this notion of inference by first presenting the
elimination rule for implication. We will see 
that this rule not only formalizes Aristotle's 
modus ponens rule of reasoning (it is one of
his fundamental "syllogisms"), but is also
corresponds to funtion application! 

EXERCISE: When you apply a function that takes 
an argument of type R and returns a value of 
type W to a value of type P, what do you get? 
-/

/-
Now let's specofy that R and W are arbitrary
propositions in the type theory of Lean. And
recall that to judge R → W to be true or to
judge either R or W to be true means that we
have proofs of these propositions. We can now
give a precise rule in type theory capturing
Aristotle's modus ponens: what it means to be
a function, and how function application works.

{ R W : Prop }, pfRtoW : R → W, pfR : R
--------------------------------------- (→-elim)
                   pfW: W                


Here it is formalized as a function.
-/

def 
arrow_elim 
    { R W: Prop } (pfRtopfW : R → W) (pfR : R) :  W := 
        pfRtopfW pfR

/-
This program expresses the inference rule. The
name of the rule (a program) is arrow_elim. The
function takes (1) two propositions, R and W;
(2) a proof of R → W (itself a program that 
converts and proof of R into a proof of W;
(3) a proof of R. If promises that if it is
given any values of these types, it will 
return a proof of(a value of type) W. Given
values for its arguments it derives a proof 
of W by applying that given function to that
givenvalue. The result will be a proof of (a 
value of type) W. 

We thus now have another way to pronounce this
inference rule: "if you have a function that can
turn any proof of R into a proof of W, and if you 
have a proof of R, then you obtain a proof of W,
and you do it in particular by applying the 
function to that value."
-/

/- In yet other words, if you've got a function
and you've got an argument value, then you can 
eliminate the function (the "arrow") by applying 
the function to that value, yielding a value of
the return type. 
-/

/-
A concrete example of a program that serves as
a proof of W → R is found  in our program, from 
the 03_Conjunction chapter that turns any proof
of P ∧ Q (W) into a proof Q ∧ P (R). 

We wrote that code so that for any propositions, 
P and Q, for any proof of P ∧  Q, it returns a 
proof of Q ∧ P. It can always do this because 
from any proof of P ∧ Q, it can obtain separate 
proofs of P and Q that it can then re-assembled
into a proof of Q ∧ P. That function is a proof
of this type: ∀ P Q: Prop, P ∧ Q → Q ∧ P.  That 
says, for any propositions, P and Q, a function
of this type turns a proof of P ∧ Q into a proof
of Q ∧ P. It thus proves P ∧ Q → Q ∧ P.
-/


/-
We want to give an example of the use of the
arrow-elim rule.  In this example we use a new
(for us) capability of Lean: you can define
variables to be give given types without proofs,
i.e., as axioms. 

Here (read the code) we assume that P and Q
are arbitrary propositions. We do not say
what specific propositions they are. Next
we assume that we have a proof that P → Q,
which will be represented as a program
that takes proofs of Ps and returns proofs
of Qs. Third we assumpe that we have some
proof of P. And finally we check to see
that the result of applying impl to pfP is
of type Q.
-/

variables P Q : Prop
variable impl : P → Q
variable  pfP : P
#check (impl pfP)
#check (arrow_elim impl pfP)


/-
In Lean, a proof of R → W is given as a 
program: a "recipe" for making a proof of W 
out of a proof of R. With such a program in 
hand, if we apply it to a proof of R it will
derive a proof of W. 
-/




/-
EXAMPLE: implications involving true and false
-/

/-
Another way to read P → Q is "if P (is true)
then Q (is true)."
    
We now ask which of the following implications
can be proved?

true → true     -- if true (is true) then true (is true)
true → false    -- if true (is true) then false (is true)
false → true    -- if false (is true) then true (is true)
false → false   -- if false (is true) then false (is true)

EXERCISE: What is your intuition?

Hint: Remember the unit on true and false. Think about 
the false elimination rule. Recall how many proofs there
are of the proposition, false.
-/


/- true → true -/

 /-
 Let's see one of the simplest of all possible
 examples to make these anstract ideas concrete. 
 Consider the proposition, true → true. We can
 read this as "true implies true". But for our
 purposes, a better way to say it is, "if you 
 assume you are given a proof of true, then you 
 can construct and return a proof of true." 
     
We can also see this proposition as the type of
any program that turns a proof of true into a
proof of true. That's going to be easy! Here it
is: a simple function definition in Lean. We call
the program timpt (for "true implies true"). It
takes an argument, pf_true, of type true, i.e., 
a proof of true, as an argument, and it builds
and returns a proof of true by just returning 
the proof it was given! This function is thus
just the identity function of type true → true.
-/

def timpt ( pf_true: true ) : true := pf_true

theorem timpt_theorem : true → true := timpt

#check timpt

/-
If this program is given a proof, pf, of true,
it can and does return a proof of true. Let's
quickly verify that by looking at the value we
get when we apply the function (implication) to
true.intro, which is the always-available proof
of true. 
-/

#reduce (timpt true.intro)

/-
Indeed, this program is in effect a proof
of true → true because if it's given any
proof of true (there's only one), it then
returns a proof of true.

Now we can see explicitly that this program 
is a proof of the proposition, true → true,
by formalizing the proposition, true → true,
and giving the program as a proof!
-/

theorem true_imp_true : true → true := timpt

/-
And the type of the program, which we are
now interpreting as a proof of true → true,
is thus true → true. The program is a value
of the proposition, and type, true → true. 
-/

#check timpt





/- true → false -/

/-
EXERCISE: Can you prove true → false? If
so, state and prove the theorem. If not,
explain exactly why you think you can't
do it. 
-/

-- def timpf (pf_true : true) : false := _

-- theorem timpf_theorem: true → false := _


/- false → true -/

/-
EXERCISE: Prove false → true. The key to
doing this is to remember that applying 
false.elim (think of it as a function) to
a proof of false proves anything at all.
-/

def fimpt (f: false) : true := true.intro

theorem fimpt_theorem : false → true := fimpt


/- false → false -/

/-
EXERCISE: Is it true that false → false? 
Prove it. Hint: We wrote a program that
turned out to be a proof of true → true.
If you can write such a program, call it 
fimpf, then use it to prove the theorem,
false_imp_false: false → false.
-/

def fimpf (f: false) : false := f

theorem fimpf_theorem : false → false := fimpf

def fimpzeqo (f: false) : 0 = 1 := false.elim f

theorem fizeo : false → 0 = 1 := fimpzeqo




/-
We summarize our findings in the following
table for implication.

true  →  true  :  proof, true
true  →  false :  <no proof>
false →  true  :  proof, true
false →  false :  proof, true

What's deeply interesting here is that 
we're not just given these judgments as 
unexplained pronouncements. We've *proved*
three of these judgments. The fourth we
could not prove, and we made an argument 
that it can't be proved, but we haven't
yet formally proved, nor do even have a
way to say yet, that the proposition is
false. The best we can say at this time
is that we don't have a proof.
-/


#check true_imp_true  -- (proof of) implication
#check true.intro     -- (proof of) premise
#check (true_imp_true true.intro) -- conclusion!



/- *** → INTRODUCTION RULE -/


/-
The → introduction rules say that if 
assuming that there is proof of P allows
you to derive a proof of Q, then one can
derive a proof of P → Q, discharging the 
assumption. 

To represent this rule as an inference
rule, we need a notation to represent 
the idea that from an assumption that
there is a proof of P one can derive a
proof of Q. The notation used in most
logic books represents this notion as a
vertical dotted line from a P above to
a Q below. If one has such a derivation
then one can conclude P → Q. The idea
is that the derivation is in essence a
program; the program is the proof; and
it is a proof of the proposition, which
is to say, of the type, P → Q. 


   P
   |
   |
   Q
 -----
 P → Q


The proof of a proposition, P → Q, in
Lean, is thus a program that takes an 
argument of type P and returns a result 
of type Q.
-/

/-
Tactic-based proof scripts for implications
-/

variables R W : Prop
variable rimpq: R → W

theorem w : W :=
begin 
assume (pfR : R), 
show W, from rimpq pfR 
end

