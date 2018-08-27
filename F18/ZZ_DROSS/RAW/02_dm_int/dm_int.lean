import ..dm_nat.dm_nat

inductive integer : Type
| of_nat : natural → integer
| neg_succ_of_nat : natural → integer