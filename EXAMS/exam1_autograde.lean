import .exam1_key

-- #1 [5 points]
#check (from_a_eq_b_prove_b_eq_a : ∀ (T : Type) (a b : T), a = b → b = a)

-- #2 [5 points] (check for lambda expression)
#check (from_a_eq_b_prove_b_eq_a' : ∀ (T :Type), ∀ (a b : T), a = b → b = a)

-- #3 [10 points]
#check (t1 : forall P Q: Prop, P → Q → P ∧ Q)

-- #4 [10 points]
#check (t2 : ∀ P Q : Prop, (P ∧ Q) → (Q ∧ P))

-- #5 [10 points]
-- 
#check (arrow_trans : ∀ P Q R : Prop, (P → Q) → (Q → R) → (P → R))

-- #6 [10 points]
theorem foo : square = λ n, n * n := rfl

-- #7 -- check manually that they used a lambda expr

-- #8 [10 points] One or the other of the following is good
theorem quadRight : quad = λ a b c x, a * x * x + b * x + c := rfl
theorem quadRight' : quad = λ a b c x, a * x^2 + b * x + c := rfl

-- #9 [10 points]
#check (noContra : ∀ Q : Prop, (Q ∧ ¬ Q) → false)

-- #10 [10 points] read the answers in English
-- 
#check (contraPos : ∀ P Q : Prop, (P → Q) → (¬ Q → ¬ P))


-- #11 [10 points] -- read manually
#check (double_negation_elim : ∀ (P : Prop), ¬¬P → P)
