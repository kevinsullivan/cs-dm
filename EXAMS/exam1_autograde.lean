import .exam1_key

-- #1 [5 points]
-- ∀ (T : Type) (a b : T), a = b → b = a)
#check from_a_eq_b_prove_b_eq_a 

-- #2 [5 points] (check for lambda expression)
-- ∀ (T :Type), ∀ (a b : T), a = b → b = a
#check from_a_eq_b_prove_b_eq_a'

-- #3 [10 points]
-- : P → Q → P ∧ Q
#check t1 

-- #4 [10 points]
-- (P ∧ Q) → (Q ∧ P)
#check t2

-- #5 [10 points]
-- (P → Q) → (Q → R) → (P → R)
#check arrow_trans 

-- #6 [10 points]
theorem foo : square = λ n, n * n := rfl

-- #7 -- check manually that they used a lambda expr

-- #8 [10 points]
theorem quadRight : quad = λ a b c x, a * x^2 + b * x + c := rfl

-- #9 [10 points]
-- ∀ Q : Prop, (Q ∧ ¬ Q) → false
#check noContra 

-- #10 [10 points] read the answers in English
-- (P → Q) → (¬ Q → ¬ P)
#check contraPos 


-- #11 [10 points] -- read manually
-- ∀ (P : Prop), ¬¬P → P
#check double_negation_elim
