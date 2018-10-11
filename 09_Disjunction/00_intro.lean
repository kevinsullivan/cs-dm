/-
We start by making some assumptions
that we use in the rest of this unit.
-/

variables P Q R X Y Z: Prop
variable pfP : P
variable pfQ : Q
variable pfR : R

/-
If P and Q are propositions, then
P ∨ Q is also a proposition. It is
read as "P or Q" and is called a
disjunction. P and Q are called the
disjuncts of the disjunction P ∨ Q.
-/

/-
  **************************
  *** INTRODUCTION RULES ***
  **************************
-/

/-
In constructive logic, P ∨ Q, is
judged to be true if either a proof
of P or a proof of Q can be given.
Having a proof of both of course
allows one to give either proof to 
construct a proof of P ∨ Q.

Here are the introduction rules
written as inference rules.


  { P } Q : Prop, pfP: P
  ---------------------- (or.intro_left)
           P ∨ Q


  P { Q } : Prop, pfQ:  Q
  ----------------------- (or.intro_right)
            P ∨ Q

-/


/-
The or.intro_left rule (also or.inl
in Lean) takes a proof of P along with 
a proposition Q and builds a proof of 
P ∨ Q. No proof of Q is needed. P need
not be given explicit because it can be
inferred from the proof of P; however,
because no proof of Q is given, from 
which Q can be inferred, Q must be given
explicitly.

The or.intro_right (or.inr) rule takes 
a proof of Q along with a proposition P 
and constructs a proof of P ∨ Q. No proof
of P is required, but the proposition P 
has to be given explicitly, as there's
no proof to infer it from.

We have to provide the proposition
for the "side" of the disjunction
for which we're not providing a proof
so that Lean knows the type of each
of the disjuncts and thus the full 
type of the disjunction being proved. 
-/

/-
We can use example to state a theorem
without giving it a name.
-/
example : P ∨ false := 
  or.intro_left false pfP

example : false ∨ Q := 
  or.intro_right false pfQ

/-
EXERCISE: Prove 0=0 ∨ 0 = 1. 
-/

/-
Here's a proof that P or true 
is always true.
-/
theorem zero_right_or : 
  ∀ P : Prop, P ∨ true :=
    λ P,
      or.intro_right P true.intro

/-
EXERCISE: Prove that true ∨ Q is
always true as well. 
-/


/-
  **************************
  **** Elimination RULE ****
  **************************
-/

/-
The or.elim rule gives us an indirect way
to prove a proposition W (the goal) by 
showing first that at least one of two 
conditions holds (P ∨ Q), and in either 
case W must be true, because of both 
(P → R) and (Q → R) holding.
-/


/-
Here's the inference rule in plain text.

If P ∨ Q, then if both P → R and Q → R,
then R. 

pfPQ: P ∨ Q, pfPR: P → R, pfQR: Q → R
-------------------------------------- or.elim
                 R

As an example, suppose that (1) when it is
raining (R) the grass is wet (R → W); (2)
when the sprinkler (S) is on, the grass 
is also wet (S → W); and it is raining ∨ 
the sprinkler is on (R ∨ S). Then the grass 
must be wet (W).

Going in the other dirction, if our aim
is to prove W, then doing it by the strategy
of or elimination means showing that for
some propositions, R and S, R ∨ S is true,
and that *in either case*, W is true.

The reasoning is by considering each case
separately. R ∨ S means that at least one 
is true. We first consider a case where R
is true. Then we consider the case where S
is true. If case it's R that's true, then
we show that W follows from R → W. In case 
it's S that's true, we show that W follows
from S → W. W holds in either case and so
W holds.

Now let's see it working in Lean. We
make a few basic assumptions and then
show how to combine them using the or
elimination rule. We assume ...

1. a proof of P ∨ Q
2. a proof of P → R
3. a proof of Q → R
-/

variable porq : P ∨ Q
variable p2r : P → R
variable q2r : Q → R

/-
Now we derive and check a proof of R
by applying or.elim to these terms..
-/

#check or.elim porq p2r q2r

/-
Here's the same example using more 
suggestive names for propositions.
-/ 

-- Raining, Sprinkling, Wet are Props
variables Raining Sprinkling Wet : Prop

-- rors proves it's Raining ∨ Sprinkling.
variable rors: Raining ∨ Sprinkling

-- r2w proves if Raining then Wet
variable r2w: Raining → Wet

-- s2w proves if Sprinkling then Wet
variable s2w: Sprinkling → Wet

-- Put it all together to show Wet
theorem wet : Wet := 
  or.elim rors r2w s2w


/-
We explicate the general concept of or
elimination by wrapping a program around
it. The program makes both the argument
and the result types clear, and shows an
example application of or.elim.
-/
theorem wet' : 
  ∀ R S W: Prop, 
    (R ∨ S) → (R → W) → (S → W) → W :=
begin
  assume R S W pfRorS r2w s2w, 
  show W,
  from or.elim pfRorS r2w s2w
end

theorem wet'' : 
  ∀ R S W: Prop, 
    (R ∨ S) → (R → W) → (S → W) → W :=
begin
  assume R S W pfRorS r2w s2w, 
  -- apply or.elim
  apply or.elim pfRorS,
  -- this does backward chaining
  -- reducing goal to two subgoals
  -- one for each required implication 
    -- R → W
    exact r2w,
    -- S → W
    exact s2w
end

/-
Notice the subtle difference between using
or.elim and cases:
-/
theorem wet''' : 
  ∀ R S W: Prop, 
    (R ∨ S) → (R → W) → (S → W) → W :=
begin
  assume R S W r_or_s r2w s2w, 
  /-
  We want to show that if W follows from R
  and if W follows from S, then W follows 
  R ∨ S.
  -/
  show W, from 
    begin

    /- 
    What we need to show is that W follows
    from R ∨ S, whether because R is true and
    W follows from R or because S is true and
    W follows from S.  We consider each case 
    in turn. 
    -/
    cases r_or_s with r s,
    -- W follows from (r : R) and r2w
    show W, from r2w r,  
    -- W follows from (r : R) and s2w
    show W, from s2w s,  
    -- Thus W follows. 
    end 
    -- QED 
end


/-
Here's a proof that false is a right
identity for disjunction. That's a fancy
way of saying that P ∨ false is true if
and only if P is true. They're equivalent
propositions.
-/

theorem id_right_or : 
  ∀ P : Prop, P ∨ false ↔ P 
  :=
  λ P,
  begin
    -- consider each direction separately
    apply iff.intro, 
    -- note: missing args become subgoals

      -- Forward direction: P ∨ false → P
      -- assume a proof of P ∨ false
      assume pfPorfalse,
      -- show P by case analysis on this disjunction
      cases pfPorfalse with pfP pfFalse,
        -- case where we have a proof of P
        assumption, 
        -- case with proof of false
        exact false.elim pfFalse, 
  
      -- Reverse direction, easy
      apply or.intro_left
  end


/-
Exercise: Prove that false is also a
*left* identity for disjunction. That
is: false ∨ P ↔ P (false is on the left).
-/