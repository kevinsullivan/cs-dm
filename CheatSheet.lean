/-*******************-/
/- true introduction -/
/-*******************-/

theorem 
trueIsTrue : 
true 
:= 
true.intro

theorem 
trueIsTrue' : 
true 
:= 
begin
exact (true.intro),
end


/-*******************-/
/- false elimination -/
/-*******************-/

theorem 
fromFalse : 
∀ { P : Prop }, false → P 
:= 
λ P f, 
    false.elim f

theorem 
fromFalse' : 
∀ { P : Prop }, false → P 
:= 
begin
assume P f,
show P,
from false.elim f,
end


/-******************-/
/- and introduction -/
/-******************-/

theorem 
PandQ : 
∀ { P Q : Prop }, P → Q → P ∧ Q  
:= 
λ P Q p q, 
    and.intro p q

theorem 
PandQ' : 
∀ { P Q : Prop }, P → Q → P ∧ Q 
:= 
begin
assume P Q p q,
show P ∧ Q,
from and.intro p q 
end


/-*****************-/
/- and elimination -/
/-*****************-/

theorem 
PfromPandQ : 
∀ { P Q : Prop }, P ∧ Q → P 
:= 
λ P Q pq, 
    pq.left 

theorem 
PfromPandQ' : 
∀ { P Q : Prop }, P ∧ Q → P 
:= 
begin
assume P Q pq, 
show P,
from pq.left
end 

theorem 
QfromPandQ : 
∀ { P Q : Prop }, P ∧ Q → Q 
:= 
λ P Q pq, 
    pq.right

theorem 
QfromPandQ' : 
∀ { P Q : Prop }, P ∧ Q → Q 
:=
begin
assume P Q pq, 
show Q,
from pq.right
end 



/-**************************-/
/- implication introduction -/
/-**************************-/

/-
To prove P → Q, present a function that, 
when given an arbitrary proof of P, returns 
some proof of Q. 

So, for example, if it's actually true for
given propositions, P and Q, that P → Q, then
you would prove it by presenting a function
that on the assumption it's given a proof of
P reduces to and returns a proof of Q.

Note that this reasoning also applies when 
data types such as nat and bool are used as
P and Q. For example, a "proof" of the type, 
nat → bool, is any function that, when given 
an arbitrary n : nat returns some value of 
type bool. Use "def" rather than "theorem" 
when defining functions involving ordinary 
data types rather than proofs.
-/

def aFunc : 
nat → bool 
    := λ n : nat, ff



/-*************************-/
/- implication elimination -/
/-*************************-/

/-
Implication elimination can be used when we
have a proof of P → Q and a proof of P to
construct a proof of Q. This is Aristotle's 
modus ponens. In constructive logic a proof 
of P → Q is a function that, assuming it is
given a proof of P, reduces to a proof of Q. 
In effect, the function explains precisely 
how to derive a proof of Q from any proof of 
P. So, if pq is a proof of P → Q, and p is a 
proof of P, then by applying the function, 
pq, to p, we obtain a proof of Q.
-/

theorem 
arrowElim: 
∀ { P Q : Prop}, (P → Q) → P → Q 
:=
λ P Q pq p, (pq p)



/-*************************-/
/- forall (∀) introduction -/
/-*************************-/

/-
If P and Q are propositions, then to 
conclude ∀ p : P, Q, show that if you
assume that p is some arbitrary value 
of type P, then you can prove Q. In the
general case, Q is a proposition that
involves p. Here is a simple example 
in which we prove that for any n of 
type nat, n = n. You can see that the
proposition after the comma involves
the value bound by the ∀ before the 
comma. 
-/

theorem 
allNeqN : 
∀ N : nat, N = N
:=
begin
assume n : nat, -- assume n is arbitrary nat
show n = n,     -- prove prop true for that n
from eq.refl n  -- conclude true for all n
end



/-************************-/
/- forall (∀) elimination -/
/-************************-/

/-
Forall elimination reasons that if some
proposition is true for every value of 
a type, then it must also be true for a
specific value of that type. So from the
proposition, ∀ P, Q combined with p : P,
we conclude Q. Forall elimination is just
another form of arrow elimination and in
constructive logic is function application.
-/

theorem forallElim 
(pf: ∀ n : nat, n = n) (m : nat) : m = m
:=
pf m



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
read as "is equivalent to," as "if and only if," or (in writing) as "iff". 

Its introduction and elimination rules are equivalent to those for conjunction, but 
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
allows you to conlude P ∨ ¬ P "for free," without giving a proof of either P or of
¬ P. It is in this precise sense that em
is not "constructive." When using em, you
do not build a "bigger" proof (or P ∨ ¬ P)
from one or more "smaller" proofs (of P or 
of ¬ P). Whereas constructive proofs are
"informative," in that they contain the
smaller proofs needed to justify a given
conclusion, classical proofs are not, in
general. Accepting that P ∨ ¬ P by using
em gives you a proof but such a proof does not tell you anything at all (it doesn't inform you) which case is true.
-/



/- ************** -/
/- or elimination -/
/- ************** -/

/-
The elimination rule for or says that if
P ∨ Q is true, and if in either case--of P being true or of Q being true--some other
proposition R is true, then R must be true.

So, for example if "it's raining or the fire
hydrant is running" (P ∨ Q), and if "if it's raining then the streets are wet", and also "if the fire hydrant is running then the streets are wet", then the streets are wet!
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

/- Exists introduction -/

/-
From "Nifty is a cat" deduce "There exists a
cat." From a proof of (P a), for a particular
a, derive a proof of ∃ x, P x.
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


