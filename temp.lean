example : ∀ P Q : Prop, P → Q → P ∧ Q :=
begin
assume P Q : Prop,
assume p, 
assume q,
show P ∧ Q,
apply and.intro,
exact p,
exact q,
end

example : ∀ P Q : Prop, P ∧ Q → P :=
begin
assume P Q,
assume pandq,
apply and.elim_left pandq,
end

example : ∀ P : Prop, P → ¬ ¬ P :=
begin
assume P,
assume p,
show ¬ ¬ P,
from 
    begin
    assume np,
    have f : false := (np p),
    apply false.elim f,
    end
end

example : ∀ P Q : Prop, P ∧ ¬ P → Q :=
begin
intros P Q pandq,
--assume P Q pandq,
show Q,
from 
begin
    have f : false :=
        (pandq.right) (pandq.left),
    apply false.elim f,
end,
end

example : ∀ P Q : Prop, P ∧ Q → Q ∧ P :=
begin
intros P Q paq,
apply and.intro,
exact paq.right,
exact paq.left,
end

example : 
    ∀ R S W : Prop, R ∨ S → (R → W) → (S → W) → W :=
begin
intros R S W rors rq sq,
cases rors with pfR pfS,
exact (rq pfR),
exact (sq pfS),
end

example : ∀ P Q : Prop, P ∨ Q → Q ∨ P :=
begin
intros P Q porq,
cases porq with p q,
--exact or.intro_right Q p,
exact or.inr p,
exact or.inl q,
end

example : ∀ P Q : Prop, ¬ (P ∧ Q) → (¬ P ∨ ¬ Q) :=
begin
intros P Q npandq,
end

example : ∀ P Q : Prop, ¬ P ∧ ¬ Q → ¬ (P ∨ Q)  :=
begin
intros P Q npandq,
have np := npandq.left,
have nq := npandq.right,
assume porq,
cases porq with p q,
contradiction,
contradiction,
end

open classical
example : ∀ P Q : Prop, ¬ (P ∨ Q)  → ¬ P ∧ ¬ Q :=
begin
intros,
cases (em P) with p np,
have porq := or.intro_left Q p,
contradiction,
cases (em Q) with q nq,
have porq := or.intro_right P q,
contradiction,
apply and.intro np nq,
end


axiom em : ∀ P, P ∨ ¬ P

variable X : Prop
#reduce (em X)

example : forall P Q : Prop, P → (true ∨ false) :=
begin
intros,
cases (em P) with p np,
end




