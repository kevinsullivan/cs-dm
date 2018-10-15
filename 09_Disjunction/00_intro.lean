/-
If P and Q are propositions, then
P ∨ Q is also a proposition. It is
read as "P or Q" and is called a
disjunction. P and Q are called the
disjuncts of the disjunction P ∨ Q.
In constructive logic, one can prove
P ∨ Q from either a proof of P or a
proof of Q. This unit presents and
discusses the basic introduction and
elimination rules for or.
-/

/-
We start by making some assumptions
that we use in the rest of this unit.
-/

variables P Q R X Y Z: Prop
variable pfP : P
variable pfQ : Q
variable pfR : R

/-
  **************************
  *** INTRODUCTION RULES ***
  **************************
-/

/-
In constructive logic, P ∨ Q is 
true if either a proof of P or 
a proof of Q can be given. Having 
a proof of both of course allows 
one to give either proof to prove
P ∨ Q.

Here are the introduction rules
written as inference rules.


  { P } Q : Prop, pfP: P
  ---------------------- (or.intro_left)
           P ∨ Q


Notice in the preceding rule that while
P can be inferred from pfP, Q has to be
given explicitly, because otherwise there
is no way to know what it is.

  P { Q } : Prop, pfQ:  Q
  ----------------------- (or.intro_right)
            P ∨ Q

Now P has to be given explicitly, while
Q can be inferred.
-/


/-
The or.intro_left rule takes 
propositions P and Q (P implicitly)
constructs a proof of P ∨ Q. No proof 
of Q is needed. P need not be given 
explicitly because it can be inferred 
from the proof of P; however, because 
no proof of Q is given, from which Q 
could be inferred, Q must be given
explicitly.

The or.intro_right rule takes 
a proof of Q explicitly along with a 
proposition P, from which P is inferred, 
and constructs a proof of P ∨ Q. No proof
of P is required, but the proposition P 
has to be given explicitly, as there's
no proof to infer it from.
-/

/-
To prove a disjunction, such as 
0 = 0 ∨ 0 = 1, we have to pick which
side of the disjunction we will give
a proof for in order to apply or.intro.
Here's an example. We pick the side
to prove that actually has a proof.
There is no proof of the right side.
-/

theorem goodSide : 0 = 0 ∨ 0 = 1 :=
   or.intro_left (0=1) (eq.refl 0)
  ---------------- Q ---pfP

/-
Recall that we can use "example" in
Lean to state a theorem without giving 
its proof a name. 

Here we use example to state and prove 
that for any proposition, P, P or false 
is equivalent to P. (Remember that we 
assumed above that P is defined to be a
Prop, and pfP is defined to be a proof 
of P.)
-/
example : P ∨ false := 
  or.intro_left false pfP

example : false ∨ Q := 
  or.intro_right false pfQ

/-
EXERCISE: Prove 0 = 1 ∨ 0 = 0. 
-/

theorem xyz : 0 = 1 ∨ 0 = 0 :=
  or.intro_right (0 = 1) rfl

/-
Here's a proof that P or true 
is always true. The key idea is
that we can always choose to give
a proof for the true side, which
is trivial.
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
to prove a proposition, R, (the goal) by 
showing first that at least one of two 
conditions holds (P ∨ Q), and in either 
case W must be true, because both (P → R)
and (Q → R). If P ∨ Q, then if both P → R 
and Q → R, then R. 

Here's the inference rule in plain text.

pfPQ: P ∨ Q, pfPR: P → R, pfQR: Q → R
-------------------------------------- or.elim
                 R

-/

/-
As an example, suppose that (1) when it 
is raining (R) the grass is wet (R → W); (2)
when the sprinkler (S) is on, the grass 
is also wet (S → W); and it is raining *or* 
the sprinkler is on (R ∨ S). Then the grass 
must be wet (W).

Going in the other direction, if our aim
is to prove W, we can do it using or.elim
by showing that for some propositions, R 
and S, that R ∨ S is true, and that *in 
either case*, W must also be true.

The reasoning is by considering each case,
each possible way to have proven R ∨ S,
separately. R ∨ S means that at least one
of R and S is true, and for whichever one
is true, there must be a proof. 

We first consider a case where R is true. 
Then we consider the case where S is true. 
In the case where R is true, we show that 
W follows from R → W. In case where S is
true, we show that W follows from S → W. 
W holds in either case and so W holds.
-/


/-
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
The following program make the arguments to
and the result of or.elim clear, and it 
gives an example of the use of or.elim.
-/
theorem orElim : 
  ∀ R S W: Prop, 
    (R ∨ S) → (R → W) → (S → W) → W 
:=
begin
  assume R S W rors r2w s2w, 
  show W,
  from or.elim rors r2w s2w
end

/-
This example constructs the same
proof but illustrates how we can
apply inference rules, leaving out
some arguments, to be filled in, in
the style of backward reasoning.
-/
theorem orElim' : 
  ∀ R S W: Prop, 
    (R ∨ S) → (R → W) → (S → W) → W :=
begin
  assume R S W rors r2w s2w, 
  -- apply or.elim
  apply or.elim rors,
  -- reduce goal to two subgoals
  -- one for each required implication 
    exact r2w,
    exact s2w
end

/-
Notice the subtle difference between using
or.elim and cases. The or.elim rule takes
the disjunction and the two implications as
arguments. The cases tactic, on the other
hand, sets you up to apply one or the other
implication depending on the case being
considered.
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
We recommend approaching proofs from
disjunctions, as here, using the cases
tactic. It clearly shows that what is
happening is a case analysis. That if
the disjunction is true, then one way
or another we can reach the desired
conclusion.
-/

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
Another example. The proof of another
standard rule of reasoning in natural 
deduction.
-/
theorem disjunctiveSyllogism :
  ∀ P Q : Prop, P ∨ Q → ¬Q → P :=
begin
  intros P Q porq nq, -- assumptions
  cases porq with p q, -- now by cases
    assumption, -- case where p is true,
    exact false.elim (nq q) -- or q true
end


/-
Exercise: Prove that false is also a
*left* identity for disjunction. That
is: false ∨ P ↔ P (false is on the left).
-/

