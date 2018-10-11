variables P Q R X Y Z: Prop
variable pfP : P
variable pfQ : Q
variable pfR : R

/-
If P and Q are propositions, then
P ∨ Q is also a proposition. It is
read as "P or Q" and is called a
disjunction. P and Q are called the
disjuncts.

In constructive logic, P ∨ Q, is
judged to be true if either a proof
of P or a proof of Q can be given.
Having a proof of both of course
allows one to give either proof to 
construct a proof of P ∨ Q.

Here are the introduction rules.


  { P } Q : Prop, pfP: P
  ---------------------- (or.intro_left)
           P ∨ Q


  P { Q } : Prop, pfQ:  Q
  ----------------------- (or.intro_right)
            P ∨ Q

-/

/-
  **************************
  *** INTRODUCTION RULES ***
  **************************
-/

/-
The or.intro_left rule takes a 
proof of P along with a proposition 
Q and builds a proof of P ∨ Q. (No 
proof of Q is needed so any Q will 
do, even false.) 

The or.intro_right rule takes a proof 
of Q along with a proposition P and
constructs a proof of P ∨ Q. No proof
of P is required, so any P will do,
even false. 

We have to provide the proposition
for the "side" of the disjunction
for which we're not providing a proof
so that Lean knows the type of both
propositions and thus the full type 
of the disjunction to be proved. 
-/

/-
We can use example to state a theorem
without giving it a name.
-/
example : P ∨ false := 
  or.intro_left false pfP

example : false ∨ P := 
  or.intro_right false pfP

/-
EXERCISE: Prove 0=0 ∨ 0 = 1. 
-/

/-
Here's a proof that true is a right
identity for or.
-/
theorem zero_right_or : 
  ∀ P : Prop, P ∨ true :=
    λ P,
      or.intro_right P true.intro

/-
EXERCISE: Prove that it's also a left
identity.
-/


/-
  **************************
  **** Elimination RULE ****
  **************************
-/

/-
The elimination rule for ∨ at first
seems slightly involved. Here's what
it says:

If P ∨ Q, and if both P → R and Q → R,
then R. 

pfPQ: P ∨ Q, pfPR: P → R, pfQR: Q → R
-------------------------------------- ∨-elim
                 R

For example, suppose that (1) when it is
raining the grass is wet (P → R); when the
sprinkler is on, the grass is wet (Q → R);
and it is raining or the sprinkler is on
(P ∨ Q). Then the grass must be wet (R).

The reasoning is by cases. P ∨ Q means at
least one of them is true. If it's P, then
we can show that R is true using P → R. If 
it's Q, then we can show from R using Q → R. 
So in either case, we can show R, so R must
be true.
-/

variable porq : P ∨ Q
variable p2r : P → R
variable q2r : Q → R
#check or.elim porq p2r q2r

/-
Here's the same example using
more suggestive proposition names. 
-/
variables Raining Sprinkling Wet : Prop
variable r2w: Raining → Wet
variable s2w: Sprinkling → Wet
variable rors: Raining ∨ Sprinkling
theorem wet : Wet := or.elim rors r2w s2w

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
  apply or.elim pfRorS,
  exact r2w,
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
  assume R S W pfRorS r2w s2w, 
  cases pfRorS with pfR pfS,
  exact r2w pfR,
  exact s2w pfS,
end

/-
The or.elim rule gives us an indirect way
to prove a proposition W by showing that
one or another condition must be true
(P ∨ Q), and in either case W must be 
true because both (P → R) and (Q → R).
-/

/-
Here's a proof that false is a right
identity for disjunction.
-/

theorem id_right_or : 
  ∀ P : Prop, P ∨ false ↔ P :=
    λ P,
    begin
      apply iff.intro,
      assume pfPorfalse,
      cases pfPorfalse with pfP pfFalse,
        assumption,
        exact false.elim pfFalse,
      apply or.intro_left
    end

/-
Exercise: Prove that false is also a
left identity for disjunction.
-/