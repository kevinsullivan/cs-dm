import .exam1_key

/- *******
AUTOGRADER
******* -/

def x : nat := 5

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

-- Extra credit [5 points] 
#check (double_negation_elim : ∀ (P : Prop), ¬¬P → P)

theorem 
disjunctiveSyllogism :
forall P Q : Prop, P ∨ Q → ¬Q → P 
:=
begin
intros P Q porq nq, -- assumptions
cases porq with p q, -- now by cases
assumption, -- case where p is true,
exact false.elim (nq q) -- or q true
end

theorem resolution :
forall P Q R : Prop,
    (P ∨ Q) ∧ (¬ Q ∨ R) → (P ∨ R)
:=
begin
-- introduce assumptions
intros,
-- get individual disjunctions
have pq := a.left,
have nqr := a.right,
-- pf by case analysis on P ∨ Q
cases pq with p q,
-- case where p is true
from or.inl p,
-- case where q is true
cases nqr with nq r,
exact false.elim (nq q),
from or.inr r,
-- qed
end


-- Socrates' MP (with predicates)
-- for presentation in predicate unit
theorem modpon: 
∀ Being : Prop,
∀ isPerson : Being → Prop,
∀ isMortal : Being → Prop,
∀ (p : Being), 
    (isPerson p → isMortal p) → 
    ∀ socrates : Being, 
    isPerson socrates → isMortal socrates
:=
begin
intro Being,
intro isPerson,
intro isMortal,
intro aBeing,
intro peopleAreMortal,
intro socrates,
intro socratesIsAPerson,
show isMortal socrates,
from peopleAreMortal socratesIsAPerson,
end

theorem modpon': 
∀ Being : Prop,    -- Type doesn't work
∀ isPerson : Being → Prop,
∀ isMortal : Being → Prop,
∀ (p : Being), 
    (isPerson p → isMortal p) → 
    (∀ socrates : Being, 
        isPerson socrates → 
        isMortal socrates)
:=
begin
intro Being,
intro isPerson,
intro isMortal,
intro aBeing,
intro peopleAreMortal,
intro socrates,
intro isPersonSocrates,
show isMortal socrates,
from peopleAreMortal isPersonSocrates,
end

theorem foo :
∀ T : Type,
∀ P : T → Prop,
∀ M : T → Prop,
(∀ t : T, P t → M t) -> 
(∃ u : T, P u)z → M u :=
begin
intros,
exact (a a_1)
end
