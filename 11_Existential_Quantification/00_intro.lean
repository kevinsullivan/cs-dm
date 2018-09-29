/- ***********************-/
/- *** ∃ Introduction *** -/
/-************************-/

/-
An existentially quantified 
proposition asserts that there
is some value of some type for 
which some proposition involving 
that value is true. Here's an 
example.
-/

def anExistsProp := 
    exists m , m + m = 8

/- This proposition asserts that 
there is some value m (inferred 
to be of type ℕ) that makes the 
sub-proposition, m + m = 8, true. 

Basic algebra tells us that there 
is such a value, namely 4, so this 
proposition can be proved. 

The key thing to remember is that
a proof of such an existentially
quantified proposition is a pair.
The first element is a value that 
makes the sub-proposition true. We
call such a value a "witness". The 
second element is a proof of the 
sub-proposition when the witness
is substituted in. 

So a proof of the proposition, 
exists m , m + m = 8, for example,
will be a pair, where the first
element is the ℕ value 4 and the
second element is a proof of the
proposition that 4 + 4 = 8 (which 
can be produced using rfl).
-/

/-
More generally the introduction 
rule for ∃ is as follows:

(T : Type) (p: T → Prop) (w : T) (e : pred wit)
-----------------------------------------------
            ∃ a : T, pred a
-/

#print exists.intro

def existsIntro 
    (T: Type) 
    (pred: T → Prop) 
    (w : T) 
    (e : pred w) 
    : exists w, pred w
    := exists.intro w e

/-
Abstract example
-/
variable T : Type
variable witness : T
variable predicate : T → Prop
variable proof : predicate witness

def pf : ∃ m, predicate m := 
    ⟨ witness, proof ⟩ 

/-
Concrete example
-/

def isEven (n : nat) : Prop :=
    exists m : nat, m + m = n

def eightEven := isEven 8

#check eightEven
#reduce eightEven

lemma pf8Even : 8 = 4 + 4 := rfl

-- exact proof term using exists.intro
theorem even8 : eightEven := 
    exists.intro 4 pf8Even

-- syntactic sugar
theorem even8' : eightEven := 
    ⟨ 4, pf8Even ⟩ 

-- as a tactic script
-- unfold expands a definition
theorem even8'' : isEven 8 := 
begin
unfold isEven,      -- not necessary
exact ⟨ 4, pf8Even ⟩ 
end 

/-
EXERCISE: Construct a proof, isNonZ,
of the proposition that there exists 
a natural number n such that 0 ≠ n.
-/

theorem isNonZ : exists n : nat, 0 ≠ n :=
exists.intro 1 (λ pf : (0 = 1), nat.no_confusion pf)


/- **********************-/
/- *** ∃ Elimination *** -/
/-***********************-/

/-
"Notice that in this pattern of reasoning, p should be “arbitrary.” In other words, we should not have assumed anything about p beforehand, we should not make any additional assumptions about p along the way, and the conclusion should not mention p. Only then does it makes sense to say that the conclusion follows from the “mere” existence of a p with the assumed properties. 
...
"exists.elim allows us to prove a proposition 
q from ∃ x : α, p x, by showing that q follows 
from p w for an arbitrary value w" -- Avigad
-/

def existsElim 
    { S : Type } 
    { pred : S → Prop }
    ( P : Prop)
    ( ex : exists x, pred x) 
    ( p2t : ∀ x : S, pred x → P) : P
    :=
        exists.elim ex p2t

/-
The preceding formulation of a function that
does ∃ elimination makes clear what pieces have
to be "assembled" for exists.elim to work.

The following is a restatement of the same 
function, but now it returns a higher order function that takes as an argument a proof 
of the proposition, ∀ x : S, pred x → T. In
this form, it better clarifies what you have
to provide, along with a proof of "exists x, 
pred x", to use ∃ elimination.

In a nutshell, the proof of the ∃ shows that
there is some value with the required property.
The ∀ shows that no matter which such value you
pick, you can derive P from a proof that it has
that property. Given these two conditions, the
exists.elim rule allows you to conclude that P
is true.
-/

def existsElim' 
    { S : Type } 
    { pred : S → Prop }
    ( P : Prop)
    ( ex : exists x, pred x) :
    ( ∀ x : S, pred x → P) → P
    :=
        λ p2t : (∀ x : S, pred x → P),
            exists.elim ex p2t