/- *** Introduction *** -/
inductive dm_prod (α β : Type)
| mk : α → β → dm_prod


/- Example -/
def pr01 : dm_prod nat nat := dm_prod.mk 0 1
#check pr01
#reduce pr01



/- *** Elimination *** -/
def dm_fst { α β : Type } : dm_prod α β → α
| (dm_prod.mk a b) := a

def dm_snd { α β : Type } : dm_prod α β → β
| (dm_prod.mk a b) := b


/- Examples -/
#check dm_fst pr01
#reduce dm_fst pr01
#check dm_snd pr01
#reduce dm_snd pr01



