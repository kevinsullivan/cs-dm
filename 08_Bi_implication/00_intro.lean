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
The logical way to read this is as
saying that if we assume that P and 
Q are propositions, ...
-/

section bi_impl
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

#check iff.intro forward backward

/-
Going the other way, if we're given a 
proof of P ↔ Q, then we can derive proofs
of P → Q and of Q → P using the iff.elim
left and right rules.
-/

#check  iff.elim_left (iff.intro forward backward)
#check  iff.elim_right (iff.intro forward backward)


/-
Warmup: Function composition.
-/

/-
Warmup. If we have a function from P to Q 
and another function from Q to R then we 
can derive a function from P to R by way
of Q.

{ P Q : Prop } (pq : P ↔ Q) (qr : Q ↔ R) 
---------------------------------------- compose
              pr : (P ↔ R)

Verify that compose is a valid reasoning
principle by proving it with a function
that takes as its arguments: propositions 
P, Q, and R (implicitly); and proofs of 
P ↔ Q and of Q ↔ R; and that derives a 
proof of P ↔ R.
-/

def compose : ∀ { P Q R : Type }, (P → Q) → (Q → R) → (P → R) := 
        /-
        To prove this type, we ...
        -/
 
        /-
        Assume P, Q, and R are types
        -/
        (λ P : Type, 
        (λ Q : Type,
        (λ R : Type,
        
        /-
        Assume we're given functions, pq and 
        qr, of types P → Q and Q → P, respectively
        -/
        (λ pq : P → Q,
        (λ qr : Q → R,

        /-
        Now show (produce a function of type)
        P → R, by ...
        -/
        
        /-
        assume a proof of P, ...
        -/
        (λ p : P,

        /-
        then return (a value of type) R.
        -/
        qr (pq p)  

        ) ) ) ) ) )

/-
Suppose that P, Q, and R are propositions,
and that P → Q express the idea that if it 
is raining the streets are wet, and that 
Q → R express the idea that if the streets 
are wet then it takes longer to stop. From 
these assumptions we can deduce P → R: if 
it's raining then it takes longer to stop.

We can prove that this is a logically valid
form of reasoning by writing this inference
rule:

{ P Q : Prop } (pq : P ↔ Q) (qr : Q ↔ R) 
---------------------------------------- compose
              pr : (P ↔ R)
-/

/-
The name, "hypothetical syllogism", or
"chain rule" is given to a reasoning
principle based on the  chaining of two 
implications: first reasoning from P to 
R then from R to P to reason from P to R.

Here's an example.

Suppose P, Q, and R are propositions, 
that P → Q express "if it's raining then 
the streets are wet,"" and Q → R, "if the
streets are wet then it takes longer to 
stop." From these assumptions we can deduce 
that if "it's raining (P) then it takes 
longer to stop (R).

{ P Q : Prop } (pq : P → Q) (qr : Q → R) 
---------------------------------------- chain
              pr : (P → R)


As usual we can prove this rule to be valid
by stating and proving it formally. Here's 
a logically clear formulation of the rule 
along with a proof that it is valid.
-/

def chain : ∀ { P Q R : Prop }, (P → Q) → (Q → R) → (P → R) := 
        /-
        To prove this proposition, we ...
        -/
 
        /-
        assume P, Q, and R are propositions...
        -/
        (λ P : Prop, 
        (λ Q : Prop,
        (λ R : Prop,
        
        /-
        and assume we're given proofs of P → Q and Q → P
        -/
        (λ pq : P → Q,
        (λ qr : Q → R,

        /-
        Now we show P → R by ...
        -/
        
        /-
        first assuming a proof of P ...
        -/
        (λ p : P,

        /-
        then deriving a proof of R.
        -/
        qr (pq p) 

        ) ) ) ) ) )


/-
We can leave out the explicit types and let
Lean infer them from context.
-/

def chain' : ∀ { P Q R : Prop }, (P → Q) → (Q → R) → (P → R) := 
        (λ P, (λ Q, (λ R, (λ pq,(λ qr, (λ p,qr (pq p) ) ) ) ) ) )


/-
We also don't need the parenthesis, as the
lambda expressions associate to the right in
any case.
-/
def chain'' : ∀ { P Q R : Prop }, (P → Q) → (Q → R) → (P → R) := 
        λ P, λ Q, λ R, λ pq, λ qr, λ p, qr (pq p)

/- Finally, Lean lets us use a single λ followed 
by names for multiple arguments, giving us the
simplest statement of this theorem, nevertheless
equivalent to all of those above.
and every argument. 
-/

def chain''' : ∀ { P Q R : Prop }, (P → Q) → (Q → R) → (P → R) := 
        λ P Q R pq qr p, qr (pq p)  


/-
We could also have written tactic scripts.
Here we could have written the first assume
across three lines.
-/

def chain_tactic : ∀ { P Q R : Prop }, (P → Q) → (Q → R) → (P → R) :=
begin
        assume P Q R: Prop,
        assume pq : P → Q,
        assume qr : Q → R,
        show P → R, 
                assume p : P,
                show R,
                from qr (pq p) 
end

/-
We can leave out the explicit types and run
all the assume lines together here, as well,
yielding this more concise, albeit perhaps
less immediately understandable, script.
-/
def chain_tactic' : ∀ { P Q R : Prop }, (P → Q) → (Q → R) → (P → R) :=
begin
        assume P Q R pq qr p,
        show R,
        from qr (pq p) 
end

/-
Finally, you can write the same theorem in 
the form of an ordinary function definition,
in which case assumptions are reflected in
the arguments, the return type is explicit,
and the body of the function is just as it
is in all the preceding examples. The return
type could be left implicit here, but that 
would make the code harder to understand, as
it would force the reader to figure out the
type of "qr (pq p)".
-/

def chain_prog (P Q R : Prop) (pq: (P → Q)) (qr: Q → R) (p : P): R :=
        qr (pq p) 






def compose { P Q R : Prop } (pq : P ↔ Q) (qr: Q ↔ R) 
        : P ↔ R :=
        iff.intro
                (compose (qr.left) (pq.left) )
                (compose (qr.right) (qr.left) )


/-
def iff_compose (P Q R: Prop) (pq: P ↔ Q) (qr: Q ↔ R) : P ↔ R :=
        iff.intro 
                (compose ) 
                _
-/

/-
EXERCISE:

Prove that ↔ is transitive. That is, if you
assume P, Q and R are arbitrary propositions, 
and that you have proof of P ↔ Q and of Q ↔ R,
then you can derive a proof of P ↔ R.
-/

∀ 



/-
Prove ∀ P : Prop, P ↔ (P → P)
-/



theorem foo: ∀ P : Prop, P ↔ (P → P),
        assume (P : Prop) (pfbi: P ↔ (P → P)),
        have forward := pfbi.left,        
        have backward := pfbi.right,






/-
A proof of P ↔ Q is essentially a 
proof of the conjunection (P → Q) ∧  
(Q → P). iff.intro is like ∧-intro,
and the left and right iff.elim 
rules are like the ∧-elim left and
right rules.
-/

/-
If you have a proof of P ↔ Q, it
tells you P and Q are equivalent.
From a classical perspective, 
qhenever P is true, so is Q, and
whenever Q is true, so is P. 

When given the goal of proving a
bi-implication,

. It takes any values,
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
theorem easy_iff: 0 = 0 ↔ 1 = 1 :=
begin
apply bi_implication,
exact λ e, eq.refl 1, -- ignores argument
exact λ e, eq.refl 0, -- ignores argument
end

/-
EXERCISES: TBD.
-/

