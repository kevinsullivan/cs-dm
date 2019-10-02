/-
-/

section homework

variables P Q R S : Prop

example : (P → (Q → R)) → (P ∧ Q → R) := 
    sorry

example : P ∧ (P → Q) → Q :=
assume h : P ∧ (P → Q),
have p : P := h.left,
show Q,
from h.right p

example : P → ¬ (¬ P ∧ Q) :=
assume p: P,
assume c: (¬ P ∧ Q),
have np: ¬ P := c.left,
show false,
from np p

example : ¬ (P ∧ Q) → (P → ¬ Q) :=
assume h : ¬ (P ∧ Q),
assume p : P,
sorry

example (h₁ : P ∨ Q) (h₂ : P → R) (h₃ : Q → S) : R ∨ S :=
sorry

example (h : ¬ P ∧ ¬ Q) : ¬ (P ∨ Q) :=
sorry

example : ¬ (P ↔ ¬ P) :=
sorry 

/-
Prove P → ¬ ¬ P without using
the axiom of the excluded middle.

Can you prove ¬ ¬ P → P without using
the axiom of the excluded middle. Explain.

Can you prove (P → Q) → (¬ Q → ¬ P) 
"intuitionistically" (without relying
directly or indirectly on the axiom 
of the excluded middle)? If so, prove 
it intuitionistically. If not, explain 
exactly where you get stuck and then
prove it "classically" (where you can
use, directly or indirectly, the axiom
of the excluded middle).

Can you prove (¬ Q → ¬ P) → (P → Q)
"intuitionistically" (without relying
directly or indirectly on the axiom 
of the excluded middle)? If so, prove 
it intuitionistically. If not, explain 
exactly where you get stuck and then
prove it "classically" (where you can
use, directly or indirectly, the axiom
of the excluded middle).
-/


Commutativity of ∧: A∧B↔B∧A
Commutativity of ∨: A∨B↔B∨A
Associativity of ∧: (A∧B)∧C↔A∧(B∧C)
Associativity of ∨ (A∨B)∨C↔A∨(B∨C)
Distributivity of ∧ over ∨: A∧(B∨C)↔(A∧B)∨(A∧C)
Distributivity of ∨ over ∧: A∨(B∧C)↔(A∨B)∧(A∨C)
(A→(B→C))↔(A∧B→C).
(A→B)→((B→C)→(A→C))
((A∨B)→C)↔(A→C)∧(B→C)
¬(A∨B)↔¬A∧¬B
¬(A∧B)↔¬A∨¬B
¬(A∧¬A)
¬(A→B)↔A∧¬B
¬A→(A→B)
(¬A∨B)↔(A→B)
A∨⊥↔A
A∧⊥↔⊥
A∨¬A
¬(A↔¬A)
(A→B)↔(¬B→¬A)
(A→C∨D)→((A→C)∨(A→D))
(((A→B)→A)→A)

Give a natural deduction proof of ¬(A∧B)→(A→¬B).
Give a natural deduction proof of (A→C)∧(B→¬C)→¬(A∧B).
Give a natural deduction proof of (A∧B)→((A→C)→¬(B→¬C)).
Take another look at Exercise 3 in the last chapter. Using propositional variables A, B, and C for “Alan likes kangaroos,” “Betty likes frogs” and “Carl likes hamsters,” respectively, express the three hypotheses in the previous problem as symbolic formulas, and then derive a contradiction from them in natural deduction.
Give a natural deduction proof of A∨B→B∨A.
Give a natural deduction proof of ¬A∧¬B→¬(A∨B)
Give a natural deduction proof of ¬(A∧B) from ¬A∨¬B. (You do not need to use proof by contradiction.)
Give a natural deduction proof of ¬(A↔¬A).
Give a natural deduction proof of (¬A↔¬B) from hypothesis A↔B.



end homework