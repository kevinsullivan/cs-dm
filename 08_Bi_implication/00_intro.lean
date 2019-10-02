/-
If P and Q are propositions, then
so is P ↔ Q. We call this form of
proposition a bi-implication. It
means P → Q ∧  Q → P. 

Here's a somewhat silly example:
if it has been raining the ground
in the desert is wet (R → W) and
if the ground in the desert is wet
then it has been raining (W → R).
In this case, we can say that the
ground in the desert is wet "if and
only if" (iff) it has been raining.

In such a situation we say that 
"it has been raining" and "the
ground in the desert is wet" are
equivalent, as the two states of
affairs invariable occur or do not
occur together.

The rules for ↔ introducing and 
elimination are conceptually the same 
as for ∧ applied to two implications,
one going in each direction (R to W
and W to R, respectively).

We recommend that you pronounce 
P ↔ Q as "P and Q are equivalent".
Most mathematicians pronounce it
as "P if and only if Q", which 
they generally abbreviate P iff
Q (note the extra f). Figuring 
out why the phrase "if and only 
if" actually makes sense is arguably 
more trouble than it's worth. Just
know that people use this phrase
in mathematics and logic all the 
time. 

 /- 
  *************************
  *** Introduction Rule ***
  *************************
-/
   
To construct a proof of P ↔ Q you 
must have (or have assumed) proofs
of two propositions: a proof of   
P → Q, and a proof of Q → P. The
inference rule is thus as follows:

P Q : Prop, p2q : P → Q, q2p: Q → P
-----------------------------------
        PiffQ : P ↔ Q

In informal mathematical writing, a 
proof of P ↔ Q will start with the
following kind of language. "We are
to prove P ↔ Q. To prove it we must
first prove P → Q, then we must prove
P → Q. We consider the case P → Q 
first. " "first we consider the implication
from P to Q, ..." Once that part
is proved, it will say "and now 
we consider the implication in
the other direction." When that
part is also done, it will then 
say, combing these results thus 
proves P ↔ Q. QED."

Lean provides the iff.intro rule
to construct a proof of P ↔ Q 
from the requisite sub-proofs.
Here's an example of its use
in a program whose type makes
clear what's required to use it.
-/

lemma bi_implication : 
 ∀ { P Q : Prop }, 
    (P → Q) → (Q → P) → (P ↔ Q) :=
        λ P Q pfPQ pfQP, 
            iff.intro pfPQ pfQP

/-
The logical way to read this is as
saying that if we assume that P and 
Q are propositions, and if we assume
we're given a proof of P → Q and we
furthermore assume we're given a
proof of Q → P then we can derive a
proof of P ↔ Q by appealing to (by
applying) the iff introduction rule
of the natural deduction system of
logical reasoning.
-/

/-
Let's assume we have two propositions,
P and Q.
-/

variables P Q : Prop

/- 
and that we have proofs of both P → Q 
and of Q → P
-/
variable forward: P → Q
variable backward: Q → P


/-
then we can apply iff-intro to derive 
a proof of P ↔ Q.  
-/

def pqEquiv := iff.intro forward backward

/-
Going the other way, if we're given a 
proof of P ↔ Q, then we can derive proofs
of P → Q and of Q → P using the iff.elim
left and right rules.
-/

#check  pqEquiv


/-
A proof of P ↔ Q is essentially a 
proof of the conjunction (P → Q) ∧  
(Q → P). iff.intro is like ∧-intro,
and the left and right iff.elim 
rules are like the ∧-elim left and
right rules.
-/

/-
EXERCISE: Construct a proof, pqequiv, of 
the proposition, P ∧ Q ↔ Q ∧ P. Note:
we don't need to know whether P and Q
are true, false, or unknown to provide
such a proof.
-/

theorem andcomm : P ∧ Q ↔ Q ∧ P :=
begin
apply iff.intro,
-- left to right
assume pq : P ∧ Q,
show Q ∧ P,
from and.intro (pq.right) (pq.left),
-- in other direction
assume qp: Q ∧ P,
show P ∧ Q,
from and.intro (qp.right) (qp.left),
end

/-
Note that the proposition that andcomm
proves is: ∀ P Q: Prop, P ∧ Q ↔ Q ∧ P.
The use of "variables P Q : Prop" above
basically adds a "∀ P Q : Prop" to each
of the propositions that follow.

As a result, andcomm in effect takes
any two propositions as arguments and
returns a proof that the conjunctions
are equivalent no matter the order of
the conjuncts.
-/

#check andcomm (0=0) (1=1)
#reduce andcomm (0=0) (1=1)

/-
In the following trivial example,
we can see how the bi_implication
introduction rule (run backwards)
gives us a way to split a goal of
proving P ↔ Q into two sub-goals,
one implication in each direction.
Knowing to do that split and then
to provide two proofs, one for each
direction, is the key to proving
bi-implications, whether using a
prover such as Lean or just using
paper and pencil.
-/
theorem easy_iff: 0 = 0 ↔ 1 = 1 :=
begin
apply bi_implication,
exact λ e, eq.refl 1, -- ignores argument
exact λ e, eq.refl 0, -- ignores argument
end

/-
EXERCISE:
1. Prove that A → B → C ↔ A ∧ B → C.
2. Given that you can prove this, does this
mean that A → B = A ∧ B?
-/

lemma a_imp_b_imp_c_iff_a_and_b_imp_c:
  ∀ A B C: Prop, (A → B → C) ↔ ((A ∧ B) → C) :=
  λ A B C: Prop,
begin
apply iff.intro,
-- forward
assume abc : (A → B → C),
assume ab : A ∧ B,
show C,
from 
  begin
  have a : A := ab.left,
  have b : B := ab.right,
  show C,
  from abc a b,
  end, 
-- backward
  assume abc : (A ∧ B → C),
  show A → B → C,
  from 
    begin
    assume (a : A) (b : B),
    have ab := and.intro a b,
    show C,
    from abc ab
    end,
end 

/- 
  *************************
  *** Elimination Rules ***
  *************************
-/


/-
As with ∧, the elimination rules,
iff.elim_left and iff.elim_right,
take a proof of P ↔ Q and return 
the constituent sub-proofs, P → Q,
and Q → P, respectively.
-/

#check iff.elim_left (andcomm P Q)
#check iff.elim_right (andcomm P Q)


theorem PIffQImpP2Q : (P ↔ Q) → P →  Q :=
begin
assume piffq p,
show Q,
from 
  begin
  have p2q := iff.elim_left piffq,
  exact (p2q p)
  end
end

-- even easier is this
theorem PIffQImpP2Q' : (P ↔ Q) → P -> Q :=
begin
assume piffq,
show P → Q,
from iff.elim_left piffq
end

/-
EXERCISE: Prove P ↔ Q) → Q -> P
-/