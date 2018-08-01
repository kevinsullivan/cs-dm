--fix imports, code is good

import .natural
import .integer

open natural
open integer

structure rational := mk_rational ::
(num : integer)
(denom : natural)
(pos : ¬ denom = O)


open rational

def zero_over_one := mk_rational (of_nat O) (S O) (by contradiction)
def one_half := mk_rational (of_nat (S O)) (S (S O)) (by contradiction)

#check mk_rational (of_nat O) (S O) (by contradiction)