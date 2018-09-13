/-
Up until now, we've said that if we can
construct a proof of a proposition, then
we can judge it to be true. We haven't 
considered false as a possible judgment.
Instead we will provide a way to judge
the proposition, ¬ P, pronounced as not
P, to be true.

¬ P is the proposition that there can 
be no proof of P, and the way that this
is expressed is with the proposition 
that if there were such a proof, it 
would lead to a contradiction, which 
is to say an inconsistency, which is 
to say, a proof of false. ¬ P is thus 
a shorthand for P → false.  If ¬ P is
true, and as there is no proof of 
false, it must be there there is no
proof of P. 

This leads us to propositions built
using the ¬ connective. Take ¬ P as an
example. What this means in Lean is
simply that P → false.
-/

theorem t1 : ¬ 1 = 0 := 
begin
by contradiction, 
end

/-
Note: in Lean, "=" binds more tightly
than "¬".
-/

#check t1


theorem  modus_tollens { P Q : Prop }
        (pfPtoQ : P → Q) (pfnQ : Q → false) : ¬ P:=
    λ (pfP : P), pfnQ (pfPtoQ pfP)

#check modus_tollens

theorem qAndNotQfalse { P Q: Prop } (pf: Q ∧ ¬ Q) : false := pf.2 pf.1

theorem notQAndNotQ: ∀ Q : Prop, ¬ (Q ∧ ¬ Q) :=
    λ (Q : Prop) (qanq : Q ∧ ¬ Q), qanq.2 qanq.1

/-
theorem proof_by_contra_1 { P Q : Prop } (pfNotPImpQNotQ: ¬ P → (Q ∧ ¬ Q)) : P :=
    _

You've got nothing in the context from which to construct a proof of P. Proof by 
contradiction is not constructive and so can't be done in plain Lean, Coq, etc.
-/

def qAndNotQimpf { Q: Prop } (pf: Q ∧ ¬ Q) : false := pf.2 pf.1
#check qAndNotQimpf

open classical

theorem proof_by_contra_1 { P Q : Prop } (pfNotPImpQNotQ: ¬ P → (Q ∧ ¬ Q)) : P :=
  by_contradiction (assume h: ¬P, show false,
   from (qAndNotQimpf (pfNotPImpQNotQ h)))

#check proof_by_contra_1
