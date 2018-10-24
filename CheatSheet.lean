/-
This cheat sheet summarizes the 
introduction and elimination
rules for each connective and
quantifier in predicate logic,
used, respectively, to construct
and to take apart, or destruct,
proofs of propositions built 
using these connectives and 
quantifiers. 
-/

/- **** -/
/- true -/
/- **** -/

/-
The proposition, true, has
a single proof and can thus
always be judged to be true. 

The introduction rule gives us
a proof without conditions.

  ---------------- (true.intro)
  true.intro: true

Having a proof of true isn't
very useful. One is always
available, and no information
can be obtained from a proof
of true. We thus don't see a
proof of true very often in
practice.
-/

/- true introduction -/


theorem trueIsTrue : true := 
    true.intro

theorem 
trueIsTrue' : true := 
begin
exact (true.intro),
end


/-*******-/
/- false -/
/-*******-/

/-
The proposition, false, has no
proofs, and can thus be judged 
to be false. Because there is 
no proof of false, there is no
introduction rule for false. On
the other hand, it often happens
in real proofs that one ends up
with inconsistent assumptions, 
which shows that such a case in
reality can't occur. When one
ends up in such a situation, a
proof of false can be derived
from the inconsistency, and the
false elimination rule can then
be used to finish the proof of
the current proof goal.
-/

/- false elimination -/

/-
From an assumed proof of false
(or from a proof of false that
is obtained from a contradiciton), 
any proposition, P, can be proved
by simply applying false.elim to
the proof of false.

  P : Prop, f : false
  ------------------- false.elim
        pf : P
-/

def fromFalse (P: Prop) (f: false) : P :=
    false.elim f

theorem 
fromFalse' : 
∀ P : Prop, false → P 
:= 
λ P f, 
    false.elim f


theorem 
fromFalse'' : 
∀ P : Prop, false → P 
:= 
begin
assume P f,
show P,
from false.elim f,
end


/-**** -/
/- and -/
/-**** -/

/-
If P and Q are propositions, then
P ∧ Q is a proposition. It is read
as asserting that both P and Q are
true. 

To prove P ∧ Q, one applies the 
introduction rule for ∧ to a proof 
of P and to a proof of Q. 

{ P, Q : Prop } (p: P) (q: Q)
----------------------------- and.intro
       ⟨ p, q ⟩ : P ∧ Q

From a proof of P and Q one can derive 
proofs of P and of Q by applying the left
and right elimination rules, respectively.

{ P Q: Prop } (pq : P ∧ Q)
--------------------------- and.elim_left
          p : P


{ P Q: Prop } (pq : P ∧ Q)
--------------------------- and.elim_right
          q : Q
-/

/- and introduction -/

-- P → Q → P ∧ Q

def PandQ (P Q : Prop) (p: P) (q: Q) : P ∧ Q :=
    and.intro p q

#check PandQ

theorem 
PandQ' : ∀ ( P Q : Prop ), P → Q → P ∧ Q  := 
λ P Q p q, 
    ⟨ p, q ⟩ -- shorthand for and.intro p q

#check PandQ'

theorem PandQ'' : ∀ { P Q : Prop }, P → Q → P ∧ Q := 
begin
assume P Q p q,
show P ∧ Q,
from ⟨ p, q ⟩, -- again shorthand for and.intro p q
end

/- and elimination -/

def PfromPandQ (P Q: Prop) (pq: P ∧ Q) : P :=
    and.elim_left pq

def QfromPandQ (P Q: Prop) (pq: P ∧ Q) : Q :=
    and.elim_right pq

theorem PfromPandQ' : ∀ { P Q : Prop }, P ∧ Q → P := 
λ P Q pq, 
    pq.left -- shorthand for and.elim_left pq

theorem QfromPandQ' : ∀ { P Q : Prop }, P ∧ Q → Q := 
λ P Q pq, 
    pq.right -- shorthand for and.elim_left pq

theorem PfromPandQ'' : ∀ { P Q : Prop }, P ∧ Q → P := 
begin
assume P Q pq, 
show P,
from pq.left
end 

theorem QfromPandQ'' : ∀ { P Q : Prop }, P ∧ Q → Q := 
begin
assume P Q pq, 
show Q,
from pq.right
end 


/- ***** -/
/- arrow -/
/-****** -/

/-
If P and Q are propositions, then P → Q
is a proposition. It read as asserting
that if P is true then Q is true. 

To prove P → Q, one must show that there
is a (total) function that, when given a 
proof of P as an argument, constructs a
proof of Q as a result. NB: Functions can
be defined to take argument of types that
have no value! See the false elimination
examples above. It is very important to
understand that P → Q being true does not 
necessarily mean that P is true, but only
that *if* P is true (there is a proof of 
P) then Q is true (a proof of Q can be 
constructed).

To prove P → Q, provide a function that
shows that from an assumed proof of P
one can construct a proof of Q. The type
of such a function is P → Q. 
-/

-- implication introduction

def falseImpliesTrue (f : false) : true :=
    true.intro

#check falseImpliesTrue

example : false → true :=
    λ f : false, true.intro

/- → implication elimination -/

/-
From a proof of P → Q and a proof of P 
one can derive a proof of Q. This is done
by "applying" the proof of the implication
(which in Lean is a function) to the proof
of P, the result of which is a proof of Q.

(P Q : Prop) (p2q: P → Q) (p : P)
--------------------------------- → elim
         (p2q p) : Q
-/

def arrowElim {P Q : Prop} (p2q: P → Q) (p : P) : Q :=
    p2q p 

theorem arrowElim': ∀ { P Q : Prop}, (P → Q) → P → Q :=
λ P Q p2q p, (p2q p)

theorem arrowElim'': ∀ { P Q : Prop}, (P → Q) → P → Q :=
begin
assume P Q p2q p,
show Q,
from p2q p
end


/- ********** -/
/- forall (∀) -/
/- ********** -/

/-
If P is a type and Q is a predicate,
then ∀ p : P, Q is a proposition. It
is read as stating that the predicate,
Q, is true for any value, p, in the 
set of values (domain of discourse)
given by the type, P. The predicate,
Q, is usually one that takes a value
of type, P, as an argument, but this
is not always the case. For example,
one could write, ∀ n : ℕ, true. Here
the predicate, true, is a predicate
that takes no arguments at all, and
so it is simply a proposition, and it
is true for every value of n, so the 
proposition, ∀ n : ℕ, true, is true.
More commonly, the predicate part of
a universally quantified proposition
will be "about" the values over which
the quantification ranges. Here is an
example: 

∀ n : ℕ : (n > 2 ∧ prime n) → odd n

This proposition asserts that any n
greater than 2 and prime is also odd
(which also happens to be true). The
predicate, (n > 2 ∧ prime n) → odd n,
in this case takes n as an argument,
and is thus "about" each of the values
over which the ∀ ranges.
-/

/- ∀ introduction -/

/-
To prove a proposition, ∀ p : P, Q, 
assume an arbitrary value, p : P,
and shows that the predicate, Q, is
true for that assumed value. As the
value was chosen arbitarily, it thus
follows that the predicate is true
for *any* such value, proving the ∀.  

To see this principle in action, 
study the following proof script.
-/

theorem allNEqualSelf: ∀ n : ℕ, n = n :=
begin
assume n, -- assume an arbitrary n
show n = n, -- show predicate true for n
from rfl, -- thus proving ∀ n, n = n
end

/- ∀ elimination -/

/-
∀ elimination reasons that if some
predicate, Q, is true for every value of 
some type, then it must also be true for 
any particular value of that type. So 
from a proof, p2q, of ∀ P, Q and a proof,
p : P, we conclude Q. 

P : Type, Q : P → Prop, p2q : ∀ p : P, Q, p : P
-----------------------------------------------
            (p2q p) :  Q p

Forall elimination is just another form 
of arrow elimination. In constructive 
logic this is function application. Study 
the following examples carefully to see 
how this works.
-/

def forallElim (p2q: ∀ n : nat, n = n) (p : nat) : p = p :=
p2q p

def forallElim' (p2q: ∀ n : nat, n = n) (p : nat) : p = p :=
begin
exact (p2q p)
end

#reduce forallElim allNEqualSelf 7



/-***********************-/
/- Negation introduction -/
/-***********************-/

/-
To prove ¬ P, show that assuming P leads to 
a contradiction (proof of false). Here's the 
intuition. ¬ P means P is false. That means that there can be no proof of P. Proving P → 
false is done by showing that there exists a 
function of type P → false. Such a function 
proves that if one can produce a proof of P,
then one can do the impossible, i.e., to
produce a proof of false. But no such proof 
exists; so, if such a function does exist, then such a proof of P does not exist. That 
is, ¬ P. 
-/

theorem 
notIntro : 
∀ P : Prop, (P → false) → ¬ P 
:=
λ P pf, pf


/- 
In both constructive and classical logic,
from the assumption that any proposition, P,
is true, we can deduce that ¬ ¬ P is true as
well. 
-/

theorem doubleNegIntro : 
∀ P : Prop, P → ¬ ¬ P :=
    λ P p np, np p



/-*******************************-/
/- (double) negation elimination -/
/-*******************************-/

/-
The rule for negation elimination in
natural deduction is really a rule 
for double negation elimination:
∀ P : Prop, ¬ ¬ P → P. 

This rule is not valid in constructive 
logic. You can't prove the following 
unless you also accept the axiom of 
the excluded middle, or equivalent.

theorem doubleNegationElim : 
    ∀ P : Prop, ¬ ¬ P → P :=
        -- we're stuck! 

However, if we accept the axiom of the 
excluded middle, which we can do by 
"opening" Lean's "classical" module, 
then we can prove that double negation 
elimination is valid. 
-/

open classical

#check em

/-
Now em is the axiom of the excluded middle.
What em tells us is that if P is any
proposition, then one of P or ¬ P is true,
and that there are no other possibilities. 

And from em we can now prove double negation elimination.  The proof is by "case analysis." 
We consider each of the two possible cases for 
P (true and false) in turn. 

If we assume P is true, then we are done, 
as our goal is to show P (from ¬ ¬ P). On 
the other hand, if we assume P is false, 
i.e., ¬ P, then we reach a contradiction, as 
both (¬ P) and ¬ (¬ P) can't be true at the 
same time. That tells us that in reality 
this case can't occur. Because there are 
no other cases, P must be true.
-/

theorem 
doubleNegationElim : 
∀ P : Prop, ¬ ¬ P → P 
:=
begin
assume P nnp,
show P,
from 
    begin
        -- proof by case analysis for P
        cases em P, -- here we rely on em
        -- case with P is assumed to be true
        exact h,
        -- case with P is assumed to be false
        exact false.elim (nnp h)
        -- em says there are no other cases
    end,
end 


/- ********************************* -/
/- bi-implication (iff) introduction -/
/- ********************************* -/

/-
A bi-implication P ↔ Q is a conjunction of
the two implications, P → Q and Q → P. It is
equivalent to P → Q ∧ Q → P. The ↔ symbol is
read as "is equivalent to," as "if and only 
if," or (in writing) as "iff". 

Its introduction and elimination rules are 
equivalent to those for conjunction, but 
specialized to the case where each of the 
conjuncts is an implication and where one 
is the other going in the other direction.

Thus, to prove P ↔ Q (introduction), you 
must first produce a proof of P → Q the you
must produce a proof of Q → P. With these
two proofs in hand, you can apply the intro 
rule to conclude P ↔ Q.
-/

theorem 
iffIntro : 
∀ P Q : Prop, (P → Q) → (Q → P) → (P ↔ Q)
:=
λ P Q pq qp, 
    iff.intro pq qp


/- ******************************** -/
/- bi-implication (iff) elimination -/
/- ******************************** -/

/-
Similarly, the iff elimination rules are
equivalent to the and elimination rules but
for the special case where the conjunction
is a bi-implication in particular.
-/

theorem
iffElimLeft : 
∀ P Q : Prop, (P ↔ Q) → P → Q
:=
λ P Q bi, 
    iff.elim_left bi


theorem
iffElimRight : ∀ P Q : Prop, (P ↔ Q) → Q → P
:=
λ P Q bi, 
    iff.elim_right bi


/- *************** -/
/- or introduction -/
/- *************** -/

/-
To prove P ∨ Q, in constructive logic
one can provide either a proof of P or
a proof of Q.
-/

theorem 
orIntroLeft: 
forall P Q: Prop, P → (P ∨ Q) 
:=
λ P Q p, 
    or.inl p

theorem 
orIntroRight: 
forall P Q: Prop, Q → (P ∨ Q) 
:=
λ P Q q, 
    or.inr q

/-
Note that the law of the excluded middle
allows you to conlude P ∨ ¬ P "for free," 
without giving a proof of either P or of
¬ P. It is in this precise sense that em
is not "constructive." When using em, you
do not build a "bigger" proof (or P ∨ ¬ P)
from one or more "smaller" proofs (of P or 
of ¬ P). Whereas constructive proofs are
"informative," in that they contain the
smaller proofs needed to justify a given
conclusion, classical proofs are not, in
general. Accepting that P ∨ ¬ P by using
em gives you a proof but such a proof does 
not tell you anything at all (it doesn't 
inform you) which case is true.
-/



/- ************** -/
/- or elimination -/
/- ************** -/

/-
The elimination rule for or says that if
P ∨ Q is true, and if in either case--of P 
being true or of Q being true--some other
proposition R is true, then R must be true.

So, for example if "it's raining or the fire
hydrant is running" (P ∨ Q), and if "if it's 
raining then the streets are wet", and also 
"if the fire hydrant is running then the 
streets are wet", then the streets are wet!
-/

theorem orElim : 
forall P Q R: Prop, 
    (P ∨ Q) → (P → R) → (Q → R) → R 
:=
begin
assume P Q R,
assume PorQ: (P ∨ Q),
assume pr: (P → R),
assume qr: (Q → R),
show R,
from or.elim PorQ pr qr 
end

-- Same idea, different identifiers
theorem orElim' : 
forall Rain Hydrant Wet: Prop, 
    (Rain ∨ Hydrant) → -- raining or hydrant on;
    (Rain → Wet) →     -- if raining then wet;
    (Hydrant → Wet) →  -- if hydrant on then wet;
    Wet                -- then wet
:=
begin
assume P Q R,
assume PorQ: (P ∨ Q),
assume pr: (P → R),
assume qr: (Q → R),
show R,
from or.elim PorQ pr qr 
end



/-
Exists (∃) introduction & elimination rules.
This material requires knowledge of predicates.
-/

/- ******************* -/
/- Exists introduction -/
/- ******************* -/

/-
From "Nifty is a cat" (that Nifty is
an object with the property of being
a cat) deduce "There exists a cat," 
asserting the existence of such an
object while hiding the particular
object that makes the proposition 
true. hiding From a proof of (P a), 
for a particular a, derive a proof 
of ∃ x, P x.
-/

#check exists.intro

theorem existsIntro :
∀ T : Type, ∀ P : T → Prop, ∀ (t : T), (P t) → ∃ x, P x
:=
begin
assume T P t pf,
show ∃ x, P x,
from (exists.intro t pf)
end

/-
The reasoning about existential elimination goes
like this. If we know that (∃ x : T, P x), then 
we can temporarily assume that there is some 
specific value, let's call it by the otherwise unused name, u, such that P u. Now, if from (P u)
we can deduce some fact S (that doesn't involve the temporarily assumed u), then we can conclude
S. So, from ∃ x, P x we deduce S, eliminating
the ∃, while also no longer relying on the
assumed value, u.
-/

#check exists.elim

def existElimExample
(T : Type) 
(P Q : T → Prop) 
(ex : exists x, P x ∧ Q x) 
: (exists y, Q y ∧ P y)
:=
exists.elim 
    ex 
    begin
    -- assume a : T a specific value ...
    assume a : T,
    -- for which the predicate is true;
    assume pfa : P a ∧ Q a,
    -- show conclusion from assumption.
    show (∃ (y : T), Q y ∧ P y),
    from 
        -- prove Q a ∧ P a
        let pa := pfa.left in
        let qa := pfa.right in
        let qp := and.intro qa pa in
        -- construct proof of goal
        exists.intro a qp
    end

/-
We will also see additional rules for equality
-/