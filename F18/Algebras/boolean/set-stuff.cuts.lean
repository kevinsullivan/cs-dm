/- TUPLE TYPES -/

/-
A tuple is an ordered list of values of specified types. Mathematicians generally write tuples as comma separated, unnamed "field" values enclosed
in parenthesis. Given that tt and ff are values of type boolean, we can 
thus define values that are 2-tuples, or pairs, of boolean values. These 
pair values include (tt, tt) and (tt, ff).
-/

/-
EXERCISE: How many such pairs are there? What are the missing pairs?
-/

/-
Here's a piece of Lean code that defines TT as a variable that has 
as its value the tuple (tt, tt). 
-/

def TT := (tt, ff)

/- 
The type of a tuple is said to be the "product type" of the given field types. 
-/

/-
The type of the tuple if the "product" of the types of its field values.
For example the type of TT = (tt, tt), is the "product type" of boolean 
and boolean, which we write as boolean × boolean. Check it!
-/

#check TT

/-
Note: You get the × symbol in Lean VS Code by typing \times. Try it!
-/


/- SETS -/

/- 
A set is understood intuitively as simply a collection of values. A value is either
in or not in a given set. A value can be in many different sets. For example, the 
natural number, 2, is in the set of even natural numbers and it is also in the set 
of prime natural numbers. (By contrast, in the theory of types, a value has exactly 
one type.) Here are two sets, to which we give names, illustrating the possibility
for a given value to be in multiple sets.

small_primes := { 2, 3, 5, 7, 11 }
small_evens  := { 2, 4, 6, 8, 10 }
-/

/- FUNCTIONS -/

/-
A function is properly understood mathematically as a set of tuples,
and in particular as a set of tuples that satisfies a major constraint: 
there is at most one tuple in the set with any given value in the first, 
or argument, position. 

Here's an example of a set of tuples for one particular function: 
{ (T, T), (F, F) }. This is what mathematicians and computer scientists
call the "identity function" on booleans. It associates each (argument) 
value, of type boolean, with itself. 

Here is another example, usually called the "negation" function on booleans:
{ (T, F), (F, T) }. It associates each value of type boolean with the other
value of type boolean: i.e., it associates true with false and false with 
true. 

EXERCISE: We have claimed that this set defines a function. That means
that it better be single-valued. Study the set and convince yourself,
and ideally someone else, that the set of tuples is indeed single valued.
-/


/-
The types of values appearing in the tuples of a function tells us the 
type of the function in question. In the preceeding examples both the
argument and result types are boolean. More generally, tf the type of 
argument values is some type, let's just call it S, and the type of the 
result values is some type, let's call it T, then we say that the type 
of the function is S → T, which we can pronounce as "S to T." 

EXERCISE: What is the type of the identify function on booleans?
EXERCISE: What is the type of the negation function on booleans?
EXERCISE: How many such functions are there from boolean to boolean?
-/



/-
When there is at most one tuple with any given value of the argument 
type, then there is at most one result value corresponding to any given
argument value. We say that functions are "single-valued". That is, if
you are given an argument value, there is at most one corresponding
result value.

If *for every* value of the argument type there is a tuple defining
a corresponding result value, then we say the function is "total". 
If there is not a tuple for each value of the argument type, we say 
that the function is partial.

EXERCISE: Think of a function from real numbers to real numbers that
is partial and explain why it is partial. 
-/

/-
If a set of tuples of a given type has  multiple tuples with the same 
argument value but different result values, then set constitutes what 
we call a "relation." Not being single-valued, however, it does not
consitute a function.

EXERCISE: Which of the following relations are and are not functions?

1. { (T, T) }
2. { (T, F), (F, T), (F, F) }
3. { (T, F), (F, T) }
-/



/- "FUNCTIONS" --- PROGRAMS THAT COMPUTE FUNCTIONS -/

/-
In practical mathematics and in computer science, we often want to 
"compute functions". For the time being, we will restrict ourselves
to discussing total functions. 

What this means is that, when given the first element of a tuple in 
the set of tuples for a given function, we want to have a mechanical 
(even mechanized!) way to determine the corresponding second element. 
For example, we might want a machine that, when given a natural number, 
n, computes and returns its square, n^2. 

Given an argument value, such as 3, for example, such a machine would 
determine that the result is 9, thereby identifying the tuple, (3, 9), 
as the one and only tuple in the set of tuples with argument value, 3.

We can view a machine that can compute a function in this sense as
being a kind of "implicit" representation of the function. It does not
explicitly enumerate a set of tuples, but given any value of the argument 
type, it will produce the corresponding result value, thus producing 
the corresponding tuple in the set of types constituting the function
in question. 

The machines we are talking about are of course just "programs."
Computer scientists routinely "abuse terminology" by referring to 
such programs as "functions." 
-/

