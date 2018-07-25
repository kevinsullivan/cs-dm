/-
An algebra is a set, A, of values of some type, along with a number of functions, f_i, that are closed over A. By the phrase, closed over A, we mean that each such functions takes
values in A as its arguments and returns values in A as its results.

In this chapter, we make this concept clear through the study of two important examples: Boolean algebra and the arithmetic of natural numbers. We characterize each algebra by first
defining its set, A, of values, and by then defining a set of functions that are closed on that particular set.

In the course of studying these two simple algebras, for which you already have strong intuition, we will encounter two of the most interesting and useful ideas in all of computer
science  and discrete mathematics: the inductive definition of sets of values, which we will call types, and the recursive definition of functions taking and returning values of
these types.
-/ 

/-
Inductive definition of the set of values of type boolean. 
-/
inductive boolean: Type
| T: boolean
| F: boolean

/-
We can confirm that the types of T and F are boolean using Lean's #check command. Hover your mouse over the #check commands.
-/
#check boolean.T
#check boolean.F

/-
We can avoid having to type the type name by using Lean's open command to "open" the "namespace" created by our definition of the type, boolean.
-/
open boolean
#check T
#check F


/-
There are four unary functions on booleans. The first is the identity function on booleans. An identity function always returns exactly the value given as an argument. Here's 
how this function is written (for our boolean type) in Lean. The "def" keyword introduces a new definition. We are defining "id_boolean". It's a function that takes a single
value, b, of type boolean. It returns a boolean value. And the specific value it returns is simply given by b, an identifier that within the scope of a function application is 
bound to whatever value the function was given as an argument.
-/
def id_boolean (b: boolean) : boolean := b

/-
Functions also have types. We can check the type of id_boolean using the #check command. Hover your mouse over the #check. You see that the type of this function is
boolean → boolean. That is, it's a function that takes a boolean and returns a boolean.
-/
#check id_boolean

/-
We can apply this function to a value and see the result using the #reduce command in Lean.
-/
#reduce id_boolean T
#reduce id_boolean F

/-
Test cases for this function. A test case asserts that the result actually obtained by applying some function to arguments is the result that is expected if the function definition
is correct. Here's a test case for id_bool. It's a little "putative theorem" followed by a proof.
-/
theorem T_id_T: id_boolean T = T := rfl

/-
Exercise: How many test cases do we need to "prove" that the function works correctly for all possible inputs. Write any additional test cases need to prove that our definition
of the identity function works as we expect it to. 
-/

/-
Congratuations, you have now constructed a "proof by case analysis". You have shown that a function works propery *for all* values of its argument type by showing that it works
for each case individually. There were only two cases to consider: when the argument is T, and when the argument is F. As the function has been shown to behave properly in each 
of these cases, we can conclude that it works properly *for all* values, of the boolean type, to which it can be applied.

Proof by case analysis often works well when you want to prove that something is true for every element in a finite set of elements. It doesn't work when the set of cases is 
infinite, of course, as it would be impossible to complete testing of each individual case. For example, in generaly you can't prove that a function that takes any natural number 
(non-negative integer) as an argument behaves correctly *for all natural numbers* by testing it on each one in turn, because you could never finish the testing process. 
-/

