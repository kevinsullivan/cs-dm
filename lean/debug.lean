/- Proof by Symmetric Property of Eq -/

theorem bySymm: ∀ α : Type, ∀ p q: α, 
    p = q → q = p 
        := λ α p q pf, eq.symm pf

/- Proof by Transitive Property of Eq -/

theorem byTrans: ∀ α: Type, ∀ p q r: α, 
    p = q → q = r → p = r 
    :=  λ α p q r pfpq pfqr, eq.trans pfpq pfqr

/- And: rfl is just shorthand for eq-refl p -/
theorem byRefl: ∀ α : Type, ∀ p : α, p = p
        := λ α p, eq.refl p

#check byRefl
#check byTrans