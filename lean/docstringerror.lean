theorem foo: ∀ P Q: Prop, P → Q → P ∧ Q :=
  λ P Q hP hQ, and.intro hP hQ