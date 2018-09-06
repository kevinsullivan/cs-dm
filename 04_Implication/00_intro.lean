/- Introduction Rule for Implication -/

/-
From two premises, (1) that "if it's raining then
the streets are wet,"" and (2) "it's raining,"" we 
can derive a conclusion with certainty. The streets
really must be wet.

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
  --------
     W

EXERCISE: As written, does this appear to be an
introduction rule or an elimination rule?

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
Aristotle's modus ponens, and what it means
to be a function!

{ R W : Prop }, pfRtoW : R → W, pfR : R
--------------------------------------- (→-elim)
                   pfW: W                
-/

/-
The inference rule says this: "If R and W are
arbitrary propositions, and if you also have 
both a proof, pfRtoW, of R → W, and you have a
proof, pfR, of R, then by applying this rule
you can obtain a proof of (and thus deduce the
truth of) W.

We thus now have another way to pronounce this
inference rule: "if you have way to turn any 
proof of R into a proof of W, and if you have
a proof of R, then you can apply the former to
the latter to obtain a proof of W."

A concrete example of a proof of W → R is found 
in our program from the conjunction chapter that 
turns any proof of P ∧ Q (here serving as W) into 
a proof of Q ∧ P (R). We wrote it so that for 
any P and Q, and no matter what proof of P ∧ Q 
might be given, it constructs a proof of Q ∧ P.
It can always do this because from any proof of
P ∧ Q, it can always apply ∧-elimination rules 
to obtain separate proofs of P and Q, and that
suffices to apply ∧-introduction to these proofs
in the opposite order, thereby obtaining the
desired proof of Q ∧ P.


We wish to emphasize two important ideas at this
point. 

First, we see here a fundmanetal strategy for 
constructing proofs, whether formal or not. We
will call it decompose-recompose. Start with the
assumptions you're given. The use elimination
rules to take them apart (decompose them) into 
pieces you need (proofs of smaller propositions).
At this point you might need to transform some
of these proofs further. And then finally use 
introduction rules to put those smaller pieces 
(proofs) back together into a proof of the the 
proposition you set out to prove. 


Second, a program that can convert any proof of
one proposition, such as R, into a proof of 
another, such as W, is in effect a proof of an 
implication: in this case, R → W. If the type 
checker accepts such a program as a proof of 
the proposition, R → W, and if you can give it
any proof of R, it will return a proof of W.

Here we thus see a second much more general 
idea. Whether you're being completely formal,
as we are here, or writing the more informal
proofs of everyday mathematics and computer
science, to prove an implication, R → W, you
must, one way or another, show that if you
assume that R is true you must be able to
apply valid reasoning principles (inference
rules) to deduce that W must be true as
well. A formal proof given as a program is
basically just a "recipe" for making a proof
of W given any argument that is a proof of 
R. With such a program in hand, if one is given
any proof of R → W,, which we can now say as,
"if you're given any program of type R → W,
and you're given any value of type R, then 
you can apply the program to the value to get
a proof of W."
-/

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

/-
EXERCISE: Is it true that false → false? 
Prove it. Hint: We wrote a program that
turned out to be a proof of true → true.
If you can write such a program, call it 
fimpf, then use it to prove the theorem,
false_imp_false: false → false.
-/

/-
EXERCISE: Prove false → true. The key to
doing this is to remember that applying 
false.elim (think of it as a function) to
a proof of false proves anything at all.
-/

def fimpf (f: false): true := 
    _


/-
EXERCISE: Can you prove true → false? If
so, state and prove the theorem. If not,
explain exactly why you think you can't
do it. 
-/


/-
We summarize our findings in the following
table for implication.

true  →  true  :  true
true  →  false :  <no proof>
false →  true  :  true
false →  false :  true

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





/- Elimination Rule for Implication -/

/-

  { P Q: Prop }, pimpq: P → Q, p : P
  ----------------------------------
                pfQ : Q
-/

#check true_imp_true  -- (proof of) implication
#check true.intro     -- (proof of) premise
#check (true_imp_true true.intro) -- conclusion!

/-
The elimination rule for implication is
Aristotle's syllogism, modus ponens. It's
also just function application! A proof 
of P → Q is a program of type P → Q. When
you apply such a program to a value (proof)
of (type) P, what do you get? A value/proof
of (type) Q.

-/



variable Person : Type 
variable Mortal : Person → Prop
def prog (p: Person) : Mortal p := sorry

-- Seven days in May