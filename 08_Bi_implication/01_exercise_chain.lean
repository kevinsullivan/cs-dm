/-
Warmup: Function composition.
-/

/-
If we know that P implies Q and that Q
implies R, we can conclude that P → R.
The name, "hypothetical syllogism", or
"chain rule" is given to this reasoning
principle.

Here's an example.

Suppose P → Q express the idea that "if 
it's raining then the streets are wet, 
and Q → R, "if the streets are wet then 
it takes longer to stop." We can deduce 
"if it's raining then it takes longer 
to stop.

This rule is sometimes called the chain
rule. It also shows that implication is
transitive. We can write it explicitly
as an inference rule:


{ P Q : Prop } (pq : P → Q) (qr : Q → R) 
---------------------------------------- chain
              pr : (P → R)


We can also verify that it's a valid 
rule by proving it. The proof will be
a function that takes P, Q, R, pq, and
qr as arguments and that derives a proof,
pr, of P → Q, the latter also a function
that assumes a proof of P and derives a
proof of R. 
-/

def chain : ∀ { P Q R : Prop }, (P → Q) → (Q → R) → (P → R) := 
        /-
        To prove this proposition, we ...
        -/
 
        /-
        assume P, Q, and R are propositions...
        -/
        (λ P : Prop, 
        (λ Q : Prop,
        (λ R : Prop,
        
        /-
        and assume we're given proofs of P → Q and Q → P
        -/
        (λ pq : P → Q,
        (λ qr : Q → R,

        /-
        Now we show P → R by ...
        -/
        
        /-
        first assuming a proof of P ...
        -/
        (λ p : P,

        /-
        then deriving a proof of R.
        -/
        qr (pq p) 

        ) ) ) ) ) )

/-
Now we explain how we can simplify this
expression by letting Lean infer types
and figure out grouping of expressions
on its own, without the parentheses.
-/


/-
We can leave out the explicit types and let
Lean infer them from context.
-/

def chain' : ∀ { P Q R : Prop }, (P → Q) → (Q → R) → (P → R) := 
        (λ P, (λ Q, (λ R, (λ pq,(λ qr, (λ p, qr (pq p) ) ) ) ) ) )


/-
We also don't need the parenthesis, as the
lambda expressions associate to the right in
any case.
-/
def chain'' : ∀ { P Q R : Prop }, (P → Q) → (Q → R) → (P → R) := 
        λ P, λ Q, λ R, λ pq, λ qr, λ p, qr (pq p)

/- Finally, Lean lets us use a single λ followed 
by names for multiple arguments, giving us the
simplest statement of this theorem. 
-/

def chain''' : ∀ { P Q R : Prop }, (P → Q) → (Q → R) → (P → R) := 
        λ P Q R pq qr p, qr (pq p)  

/-
To make the logic a little clearer, we could 
insert a lambda as follows. This might help
the reader by making it clearer that in the
context of P, Q, R, pq, and pr, we can derive
of a proof of P → R in the form of a function
that takes a proof, p : P and derives a proof
of R.
-/
def chain'''' : ∀ { P Q R : Prop }, (P → Q) → (Q → R) → (P → R) := 
        λ P Q R pq qr, 
                λ  p, qr (pq p)  

/-
We could also write the proof as a tactic script.
-/

def chain_tactic : ∀ { P Q R : Prop }, (P → Q) → (Q → R) → (P → R) :=
begin
        assume P Q R: Prop,
        assume pq : P → Q,
        assume qr : Q → R,
        show P → R, 
        from
                begin
                assume p : P,
                show R,
                from qr (pq p) 
                end
end

/-
We can leave out the explicit types and run
all the assume lines together here, as well,
yielding this more concise, albeit perhaps
less immediately understandable, script.
-/
def chain_tactic' : ∀ { P Q R : Prop }, (P → Q) → (Q → R) → (P → R) :=
begin
        assume P Q R pq qr,
        show P → R,
        from 
        begin 
                assume p,
                show R,
                from qr (pq p)
        end
end
/-
Finally, you can write the same theorem in 
the form of an ordinary function definition,
in which case assumptions are reflected in
the arguments, the return type is explicit,
and the body of the function is just as it
is in all the preceding examples. The return
type could be left implicit here, but that 
would make the code harder to understand, as
it would force the reader to figure out the
type of "qr (pq p)".
-/

def chain_prog (P Q R : Prop) (pq: (P → Q)) (qr: Q → R) (p : P): R :=
        qr (pq p) 






def compose { P Q R : Prop } (pq : P ↔ Q) (qr: Q ↔ R) 
        : P ↔ R :=
        iff.intro
                (compose (qr.left) (pq.left) )
                (compose (qr.right) (qr.left) )


/-
def iff_compose (P Q R: Prop) (pq: P ↔ Q) (qr: Q ↔ R) : P ↔ R :=
        iff.intro 
                (compose ) 
                _
-/

/-
EXERCISE:

Prove that ↔ is transitive. That is, if you
assume P, Q and R are arbitrary propositions, 
and that you have proof of P ↔ Q and of Q ↔ R,
then you can derive a proof of P ↔ R.
-/

∀ 



/-
Prove ∀ P : Prop, P ↔ (P → P)
-/



theorem foo: ∀ P : Prop, P ↔ (P → P),
        assume (P : Prop) (pfbi: P ↔ (P → P)),
        have forward := pfbi.left,        
        have backward := pfbi.right,



