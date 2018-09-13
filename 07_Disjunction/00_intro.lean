-- UNDER CONSTRUCTION

section

variables P Q R X Y Z: Prop

variable pfP : P
variable pfQ : Q
variable pfR : R

/-
There's not enough information on the right
hand side of the := to infer the value of R,
so type inference can't be used, so R must be 
given explicitly.
-/
theorem pfPorR : P ∨ R := or.intro_left R pfP

/-
EXERCISE: Explain why P doesn't need to be 
given explicitly to the right of the :=.


-/

/-

    P
  ----- (∨-intro-left)
  P ∨ Q

    Q
  ----- (∨-intro-right)
  P ∨ Q

-/

end
