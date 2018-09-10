-- UNDER CONSTRUCTION

/-
Up until now, we've said that if we can
construct a proof of a proposition, then
we can judge tit to be true. We haven't 
considered false as a possible judgment.
Instead we will provide a way to judge
the proposition, ¬ P, pronounced as not
P, to be true.

¬ P is the proposition that there can 
be no proof of P, and the way that this
is expressed is with the proposition 
that if there were such a proof, it 
would lead to a contradiction, which 
is to say an inconsistency, which is 
to say, a proof of false. ¬ P is thus 
a shorthand for P → false.  If ¬ P is
true, and as there is no proof of 
false, it must be there there is no
proof of P. 

This leads us to proposotions built
using the ¬ connective. Take ¬ P as an
example. What this means in Lean is
simply that P → false.
-/

theorem t1 : ¬ 1 = 0 := 
begin
by contradiction, 
end 