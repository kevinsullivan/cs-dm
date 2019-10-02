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

example : 0 = 1 ∨ 0 = 0 :=
  or.intro_right (0 = 1) rfl

/- 
Note: inl and inr are shorthands for 
intro_left and intro_right, and the are
defined so that the Prop parameter is 
implicit.
-/

example : 0 = 1 ∨ 0 = 0 :=
  or.inr rfl

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
always true as well, but use one 
of the shorthands to write your
proof.
-/

example : ∀ Q : Prop, true ∨ Q :=
  λ Q, or.inl true.intro


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
  apply or.elim,
  -- reduce goal to two subgoals
  -- one for each required implication
    exact rors, 
    assumption,
    exact s2w,
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
      assume p,
      exact or.inl p,
  end



/-
Another example. The proof of another
standard rule of reasoning in natural 
deduction.
-/
theorem disjunctiveSyllogism :
  ∀ P Q : Prop, P ∨ Q → ¬Q → P :=
begin
assume P Q porq,
assume nq,
cases porq with p q,
-- first case
assumption,
-- second case
exact (false.elim (nq q)),
end


/-
Exercise: Prove that false is also a
*left* identity for disjunction. That
is: false ∨ P ↔ P (false is on the left).
-/


/-
We now turn to the question, how do 
and, or, not, and implies interact?
We prove both of DeMorgan's laws, and
we also show that P → Q ↔ ¬ P ∨ Q. One
of DeMorgan's law and this identity 
about → are both classical, and not
valid/provable without the axiom of
the excluded middle (em).
-/

/-
De Morgan had two important laws. They
explain how negations distribute over
disjunctions and conjunctions.

1) ¬P ∧ ¬Q ↔ ¬(P ∨ Q)
2) ¬P ∨ ¬Q ↔ ¬(P ∧ Q)

Consider what the first of DeMorgan's
laws is saying. Start on the right. If
P ∨ Q is not true, then both P and Q
must be false, and if P and Q are both
false, then so is P ∨ Q.

Now the second law. If P and Q is false,
then at least one of P, Q must be false,
so ¬ P ∨ ¬ Q must be true. And if that is
true, then certainly P ∧ Q is false.

Proving that the first law is valid even
in constructive logic is homework 4. We 
can only prove the second law using the
axiom of the excluded middle, which we 
now proceed to do.
-/


/-
We could declare our own version of the 
axiom of the excluded middle, as we have
seen.
-/
axiom excluded_middle: ∀ (P: Prop), P ∨ ¬P

/-
Or, better, is simply to open the classical
namespace in Lean, which gives us access to
the definition, em, of this axiom. We do this
now and then show that the two propositions 
are the same. From now on, prefer to use em.
-/
open classical -- "em" is excl. middle. axiom
theorem emIse_m: em = excluded_middle := rfl


/-
And now for DeMorgan's second law.
-/
theorem DemorganLaw2 : 
  ∀ P Q: Prop, ¬P ∨ ¬ Q ↔ ¬(P ∧ Q) :=
begin

  show ∀ P Q: Prop, ¬P ∨ ¬ Q ↔ ¬(P ∧ Q), from
  begin
  -- introduce assumptions of P and Q
  assume P Q,

  -- prove implication in each direction
  apply iff.intro,

  -- first, implication in forward direction
  show ¬P ∨ ¬Q → ¬(P ∧ Q), from 
    begin
    -- goal is an implication
    -- so assume premise, and ...
    assume pf_np_or_nq,
    -- ... show conclusion
    show ¬(P ∧ Q), from
      begin
      -- remember ¬ is an implication in Lean
      -- so, assume premise, and ...
      assume pf_p_and_q,
      -- show conclusion 
      show false, from begin
        -- by case analysis on ¬P ∨ ¬Q
        cases pf_np_or_nq with pf_np pf_nq,
        -- consider case where ¬P is true
          have pf_p := pf_p_and_q.left, 
          exact pf_np pf_p,
        -- case where ¬Q is true
          have pf_q := pf_p_and_q.right,
          exact pf_nq pf_q,
        end
      end,
    end,

  -- now implication in reverse direction
    show ¬(P ∧ Q) → ¬P ∨ ¬Q, from
      begin
      -- assume premise
      assume pf_n_p_and_q,
      show ¬P ∨ ¬Q, from 
        begin
        -- consider cases for P using em
        cases (em P) with pf_p pf_np,
          -- consider cases for Q using em
          cases em Q with pf_q pf_nq,
            -- P true, Q true
            have pf_p_and_q := and.intro pf_p pf_q,
            have pf_false := pf_n_p_and_q pf_p_and_q,
            exact false.elim pf_false,
            -- P true, Q false
            exact or.intro_right (¬P) pf_nq,
          -- P false
          exact or.intro_left (¬Q) pf_np,
      end,
    end,
  end,
end

/-
Assuming the axiom of the excluded middle,
we can also show that P → Q is equivalent 
to ¬P ∨ Q. Think about what P → Q means: 
whenever P is true, Q is true. So either
P is false, in which case P → Q is true,
or Q is true (along with P). Here we use
the axiom of the excluded middle to limit
the possibilities for P to these cases.

In this proof we take a more spartan
approach to using show/from. It's really
a matter of purpose and style to use a
lot of show/from or not. It does make
proofs more self-explanatory, but it can
also make them unnecessarily verbose in
cases where they should be clear enough
in any case to one who knows how to read
this kind of code. 

Still, in the first half of this code, 
we include English language comments. In
the second half, we just leave them out.
For now we recommend that you at least
include English language comments. In 
many cases, you could then edit them
end end up with a good English language 
proof, forgetting the formalism! So you
are on your way now to understanding how
to write informal proofs.
-/

theorem altImplication:
  ∀ P Q: Prop, (P → Q) ↔ (¬P ∨ Q) :=
begin
  -- to show ∀ P Q: Prop, (P → Q) ↔ (¬P ∨ Q) 
  -- we first introduce assumptions of P and Q
  assume P Q,
  -- next we prove implication in each direction
  apply iff.intro,
    -- first we prove forward direction
    -- we start by assuming the premise
    assume pf_p_imp_q,
    -- note that without em, we're stuck
    -- key is case analysis on P given em
    cases (em P) with pf_p pf_np,
      -- case where P is true
      -- construct a proof of Q
      have pf_q := (pf_p_imp_q pf_p),
      -- then prove goal by or intro
      --exact or.intro_right (¬P) pf_q,
      exact or.inr pf_q, -- shorhand!
      -- case where ¬ P is true is easy
      exact or.inl pf_np, -- shorthand

    -- prove implication reverse direction
    assume pf_np_or_q,
    assume pf_p,
    cases pf_np_or_q with pf_np pf_q,
      have pf_false := (pf_np pf_p),
      exact false.elim pf_false,
      assumption,
end


theorem altEquivalence : 
∀ { P Q : Prop }, (P ↔  Q) ↔ ((P ∧ Q) ∨ (¬P ∧ ¬Q))
:=
begin
assume P Q,
apply iff.intro,

intros,
have pq := iff.elim_left a,
have qp := iff.elim_right a,
cases (em P) with p np,
cases (em Q) with q nq,

exact or.inl (and.intro p q),

exact false.elim (nq (pq p)),

cases (em Q) with q nq,
exact false.elim (np (qp q)),
exact or.inr (and.intro np nq),

intros,
cases a,

apply iff.intro,
intro,
exact a.2,

intro,
exact a.1,

apply iff.intro,
intro,
exact (false.elim (a.1 a_1)),

intro,
exact (false.elim (a.2 a_1)),
end

/-
Recall, that once we've prove a theorem,
we can then henceforth use it in larger
proofs. Here's an example showing how we
could use iffExplained, just proved, to
transform a goal, P ↔ Q, into the form 
of a corresponding disjunction.
-/
example : ∀ P Q : Prop, P ↔ Q :=
begin
-- Assume P and Q are propositions
intros,
-- Apply backwards implication 
-- Goal matches right side of implication
-- reducing goal to left side with substs
apply altEquivalence.elim_right,
-- abandon, never meant to complete proof
end