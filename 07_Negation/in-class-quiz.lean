/-
This in-class exercise requires solutions to two problems
-/

/-
PROBLEM #1. 

In Lean, define pf1 to be a proof of the proposition
that, "for any proposition, Q, (Q ∧ ¬ Q) → false. 

Here is a start on an answer. We use λ to 
introduce the assumption that Q is some proposition. 
The underscore is what you have to fill in. 

If you need hints, continue reading the comment
below. Once you're done with this problem, move
onto the second problem in this quiz
-/

theorem pf1 : ∀ Q : Prop, ¬ (Q ∧ ¬ Q)  :=
    λ (Q : Prop),
        ( _ )

/-
Hint #1: Remember that, assuming that A is any
proposition, ¬ A simply means (A → false).

Hint #2: Hover your mouse cursor over the underscore
in the preceding code. You will see that what you 
need to replace  it is a proof of (Q ∧ ¬ Q) → false. 
Lean writes this as ¬ (Q ∧ ¬ Q), but as you know,
the two expressions are equivalent.

Hint #3: (Q ∧ ¬ Q) → false is an implication. 
Remember what a proof of an implication looks like. 
Use a corresponding expression in place of the _.

Hint #4: Remember your elimination rules for ∧ (and).

Hint #5: Remember again: ¬ Q  means (Q → false).
If you have a proof of Q → false, then you have
a function that if it is given an assumed proof
of Q it reduces to a proof of false. Look for a
way to give this function a proof of Q!
-/

/-
PROBLEM #2.

Produce a proof, pf2, of the proposition, that 
for any propositions, P and Q, (P ∧ Q) ∧ (P ∧ ¬ Q) 
→ false. You can use the partial solution that we
gave for the last problem as a model. You'll have 
to change the name, pf1, the proposition to be 
proved, and the lambda expressions to at least
take (P Q : Prop) as an argument. Your code goes
below. Hint: Remember your and elimination rules.
Also, for this problme, you might want, but are 
not required, to use a tactic script.
-/




