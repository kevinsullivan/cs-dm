/-
If P and Q are propositions, then
so is P ↔ Q. We call this form of
proposition a bi-implication. 

What it means is that P → Q and 
Q → P. Mathematicians pronounce 
it as "P and Q are equivalent", 
or as "P if and only if Q". They
often abbreviate if and only if
as iff. P if Q means Q → P, and
P only if Q means that for P to
be true, Q must be too, which is
to say P → Q.

To prove P ↔ Q you must always
prove two propositions: first,  
P → Q, then Q → P. In informal
mathematical writing, a proof of
P ↔ Q will usually start off with
"first we consider the implication
from P to Q, ..." Once that part
is proved, it will say "and now 
we consider the implication in
the other direction." When that
part is also done, it will say,
"thus it is proved that P ↔ Q. 
QED."


 /- 
  *************************
  *** Introduction Rule ***
  *************************
-/
   
Lean provides the iff.intro rule
to construct a proof of P ↔ Q 
from the requisite sub-proofs.

-/

lemma bi_implication : 
 ∀ { P Q : Prop }, 
    (P → Q) → (Q → P) → (P ↔ Q) :=
        λ P Q pfPQ pfQP, 
            iff.intro pfPQ pfQP

/-
This "lemma" really defines a
function. It takes any values,
P and Q, of type Prop. The ∀
quantifier let's us give names
to assumed values, here of two
propositions, P and Q. In the
context in which these names 
are bound, the function further
takes an (anonymous) argument of
type (P → Q) and another of type
(Q → P), and it finally returns
a result (proof) of type P ↔ Q.

The lambda expression gives names
to all four arguments, P and Q,
pfPQ, a proof of P → Q; and pfQP, 
a proof of Q → P.

With these materials it then
reduces to a proof of P ↔ Q, 
which it produces by applying
the iff.intro rule to pfPQ and 
pfQP.  
-/

/-
Look carefully at the type of 
bi-impl. You can read it as a
function that takes a proof of
P → Q and a proof of Q → P and
that yields a proof of P ↔ Q. 
-/

variables P Q : Prop
variable p2q : P → Q
variable q2p : Q → P
#check bi_implication p2q q2p
#check iff.intro p2q q2p

/-
The second #check shows
Lean's idea of what makes
up the proof of P ↔ Q. It
is essentially a pair of
proofs, namely p2q and q2p.
-/


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

#check (iff.elim_left 
        (bi_implication p2q q2p))
#check (iff.elim_right 
        (bi_implication p2q q2p))

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
theorem fooey: 0 = 0 ↔ 1 = 1 :=
begin
apply bi_implication,
exact λ e, eq.refl 1, -- ignores argument
exact λ e, eq.refl 0, -- ignores argument
end

/-
EXERCISES: TBD.
-/

