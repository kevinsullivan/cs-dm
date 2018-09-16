/- *** Introduction *** -/

inductive dm_sum (α : Type) (β : Type)
| inl {} : α → dm_sum
| inr {} : β → dm_sum

/- Examples -/

def s1 : dm_sum nat bool := dm_sum.inl 1
def s2 : dm_sum nat bool := dm_sum.inr tt

/- *** Elimination *** -/

/- Example -/

def fixs: dm_sum nat bool → dm_sum nat bool
| (dm_sum.inl n) := dm_sum.inl (n - 1)
| (dm_sum.inr b) := dm_sum.inr ¬ b

#reduce s1
#reduce fixs s1
#reduce s2
#reduce fixs s2

