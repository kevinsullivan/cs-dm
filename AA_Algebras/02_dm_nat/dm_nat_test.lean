inductive natural : Type
    | O: natural 
    | S: natural -> natural

-- discuss semantics of this definition
--- injectivity
--- smallest set closed under finite squences of applications of constructors
--- the set of terms generated by all finite sequences of applications of the constructors

open natural

#check O
#check S O
#check S (S O)
#check S (S (S O))
-- etc.

-- abstraction
def zero_nat (n: natural): natural := 
    O 

-- abstraction
def succ_nat (n: natural): natural :=
    S n 

#eval succ_nat (S (S O)) -- KEVIN: raw rep

def pred_nat (n: natural): natural :=
    match n with
        | O := O        -- discuss: partial functions, being closed / totality
        | S n' := n'    
    end

#eval pred_nat (S (S (S O))) -- KEVIN: raw rep

def plus_natural: natural -> natural -> natural -- KEVIN: Introduce → types in very first unit
| O n2 := n2
| (S n1') n2 := S (plus_natural n1' n2)

def mult_natural: natural -> natural -> natural -- KEVIN: Introduce → types in very first unit
| O n2 := O
| (S n1') n2 := plus_natural n2 (mult_natural n1' n2)

#eval mult_natural (S (S O)) (S (S (S O)))

-- HOMEWORK: minus, exponentiate