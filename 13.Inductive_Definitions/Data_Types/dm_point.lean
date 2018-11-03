
structure point(t: Type) := mk :: (x : t) (y : t)

#check point

structure point_nat := mk :: (x : ℕ) (y : ℕ)
#check point_nat
def point_nat' := point ℕ
#check point_nat'

#check point_nat.x
#check point_nat'.x


