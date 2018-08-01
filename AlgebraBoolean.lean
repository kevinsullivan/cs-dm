/-
SUMMARY

In this chapter you will meet the following general concepts made concrete through a case study
of boolean algebra. Boolean algebra should already be familiar from your study of this algebra 
and its application to conditions and decisions in your CS 1 class.

- types and values of given types
- inductive definitions of types and their values
- tuple types and their values
- relations and functions (set theoretic view)
- functional programs as implicit representations of functions
- proof strategies:
  * by simplification and reflexivity of equality
  * by exhaustive case analysis
- algebras
- case study: boolean algebra
  * inductive definition of the type of booleans
  * functions on booleans
  ** unary functions on booleans
  ** binary functions on booleans
  ** a ternary function: if then else (tbd)
-/



/- TYPES AND VALUES: Case study of the boolean type -/

/-
A type defines a set of values and each such value has exactly that one 
type. It is important when reading and writing mathemtical logic (and code)
to be very clear about the types of the values that are being discussed or
manipulated. We already have strong intutions for many important types. They
include the booleans, the natural numbers (the non-negative integers), the
integers, the rationals, the reals, complex numbers, and also more complex
types such as lists of values of some underlying type, e.g., list of natural
number, list of boolean, list of rational, etc.

Now we are at a point where it often pays to be much more precise about 
types and values. To this end, we introduce the concept of inductive type
definitions. An inductive type definition precisely defines a set of values
(all and the only values of the type) by giving a list of "constructors", or
ways of building values of the given type. The simplest kind of constructor
is just a "constant" -- simply the name of a value of the type in question.

In this chapter, we make this idea precise, and then build on it, by giving
an inductive definition of the type of boolean values. From you earlier work
in computer science, you already know that there are just two values of this
type, in English usually called true and false, sometimes written as 1 and 0, 
respectively, and that in this chapter we will write as T and F.

Here then is an inductive definition (in the syntax of Lean language) of a
type, that we will call "boolean", that specifies T and F as the elements
of the set of values of this type. We specify two constructors: one called 
T, a value that will henceforth be taken to be of type boolean, and one 
called F, now taken to be of type boolean. The notation "T: boolean" is what
we call a type judgment, and it asserts that T is a value of type boolean.

The set of values of type boolean thus includes T and F, and it is in the
nature of inductive definitions that the *only* values of a given type are
those that can be constructed using the available constructors. The set of
values specified by the following inductive type definition is thus {T, F}.

We have written this set using "display notation", where we list the
elements of the set separated by commas and enclosed within curly braces. 
-/

inductive boolean: Type
| T: boolean
| F: boolean

/-
The observant reader will see another type judgment in this expression:
we are specifying boolean to be a value of type, "Type". "Type" is the
type of values that are themselves types in Lean!
-/

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
We can even ask what is the type of boolean! The answer will be as you will expect.
-/

#check boolean

/- TUPLE TYPES -/

/-
A tuple is an ordered list of values of specified types. Mathematicians generally write
tuple as comma separated "field" values enclosed in parenthesis. Given that T and F are
values of type boolean, for example, we can now define values that are 2-tuples, or pairs, 
of boolean values. These pair values include as (T, T) and (T, F).

EXERCISE: How many such pairs are there?

Here's a piece of code in Lean that defines TT as a variable that has the tuple (T, T) 
as its value.
-/

def TT := (T, T)

/- 
The type of a tuple is said to be the "product type" of the given field types. 
-/

#check (T, T)

/-
Here each of the field types is boolean, so the type of the tuple, (T, T), is 
the product type of boolean and boolean, which we write as boolean × boolean.

You get the × symbol in Lean by typing \times. Give it a try!

We can confirm that the type of (T, T) is as expected using Lean's #check command.
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

/- "FUNCTIONS" -/

/-
As future computer scientists and software developers, we generally don't just want
to do paper-and-pencil mathematics with sets, relations, and functions. We want to 
have computers compute with them. It's therefore vitally important to learn how to
represent functions as programs. In this course, you will learn how to do this using
what we call pure functional languages. These are languages in which every program 
defines either a value or a function that can be "applied" to data value arguments
to compute corresponding result values.
-/

/-
To be concrete, let's look at a functional program representing the identity function
on booleans.
-/

def id_boolean (b: boolean) : boolean := b

/-
The "def" keyword introduces a new definition. We give a name to our 
"function," namely "id_boolean". This function takes a single value, b, 
of type boolean, and returns value of type boolean. You can read this 
definition as saying that, "When id_boolean is applied to an argument, 
b, of type boolean, the result is a value of type boolean. In particular, 
the result that is returned is given by the expression to the right of 
the :=. That is just b. So the value that the function returns is just
the value to which it was applied. That makes this functional program
a valid representation/implementation of the identity function. 
-/

/-
We can apply this function to a value and see the result using the 
#reduce command in Lean.
-/
#reduce id_boolean T
#reduce id_boolean F

/-
Functions also have types. We can check the type of id_boolean using the #check 
command. Hover your mouse over the #check. You see that the type of this function is
boolean → boolean. That is, it's a function that takes a boolean and returns a boolean.
-/
#check id_boolean

/-
Test cases for this function. A test case asserts that the result actually 
obtained by applying some function to arguments is the result that is 
expected if the function definition is correct. Here's a test case for id_bool. 
It's a little "putative theorem" called T_id_T that asserts that the result 
of applying id_boolean to T is T. To the right of the := is a proof: the term 
"rfl". This term serves as a proof that any value is equal to itself, and it 
takes care of reducing expressions to values before deciding whether it sees
"the same" value on each side of the = sign. Here, the application of id_boolean 
to T reduces to T, and T = T, so rfl can serve as a proof that id_boolean T = T. 
-/
theorem T_id_T: id_boolean T = T := rfl

/-
Exercise: Write and prove a theorem called oeqo stating that 1 = 1.
-/

-- answer
theorem oeqo: 1 = 1 := rfl

/-
PROOF BY SIMPLIFICATION AND THE REFLEXIVE PROPERTY OF EQUALITY
-/

/-
What we see here is "proof by simplification" combined with an appeal to the reflexive 
property of equality: that everything is equal to itself! Don't worry if this all seems a 
bit mysterious at this point. We'll get into it in more detail in chapters to come.
-/

/-
Exercise: See what happens if you try to use rfl as a proof of 1 = 2
by uncommenting the following line. Hover your mouse over the red lines.
You don't need to understand the error messages that will be revealed.
You should note that somehow rfl is of the the wrong *type* to be a proof
of 1 = 2. Indeed, there is not proof of the "proposition", 1=2, because,
of course, it's simply not true!
-/
--theorem oeqt: 1 = 2 := rfl




/- PROOF BY CASE ANALYSIS -/
/-
Exercise: How many test cases do we need to "prove" that the function works correctly for all possible inputs of type boolean. (Hint: how many such inputs are there?) Write any
additional test cases need to prove that our definition of the identity function works as 
we expect it to. 
-/

/-
Congratuations, you have now constructed a "proof by case analysis" by providing that
the result of applying id_boolean to *any* boolean value is that same value. You have 
thus shown that the functional program correctly implements the identity function for
*all* booleans by showing that it works for each case individually. There were only two 
cases to consider: when the argument is T, and when the argument is F. As the function has 
been shown to behave properly in each of these cases, we conclude that it works properly 
*for all* values of its argument type.

Proof by case analysis often works well when you want to prove that something is true for every element in a finite set of elements. It isn't an appropriate proof strategy when 
the set of values to be considered is infinite, as it would be impossible to test every
individual case. For example, in general you can't prove that a functional program is
correct that takes any natural number as an argument, because there is an infinity of
such argument values. When faced with this kind of challenge, another proof strategy is
need, which goes by the name of "proof by induction." More on that later!
-/

/-
Defining functions by cases. Here's the boolean "not" function. First, the truth
table, then the computation.

 Arg Ret
+---+---+
| T | F |
+---+---|
| F | T |
+---+---+

{ (T, F), (F, T) }
-/

def neg_boolean (b: boolean): boolean :=
  match b with 
    | T := F
    | F := T
  end

/-
What is a function? A truth table view. Binary relations. Single valued. Total.

 Arg Ret
+---+---+
| T | T |
+---+---|
| F | F |
+---+---+

{ (T, T), (F, F) }
-/

/-
Binary functions: case study of the boolean "and" function

A truth table view. Binary relations. Single valued. Total.

 Arg Ret
+---+---+---+
| T | T | T |
+---+---|---+
| T | F | F |
+---+---+---+
| F | T | F |
+---+---+---+
| F | F | F |
+---+---+---+

{ (T, T, T), (T, F, F), (F, T, F), (F, F, F) }

-/

def and_boolean' (b1 b2: boolean): boolean :=
    match b1, b2 with
        | T, T := T
        | T, F := F
        | F, T := F
        | F, F := F
    end

def and_boolean (b1 b2: boolean): boolean :=
    match b1, b2 with
        | T, T := T
        | _, _ := F
    end


/- 
EXERCISES:

1. Write definitions of the following binary functions on booleans in the form of
(a) sets, using display notation, (b) truth tables, (3) functional programs.

* or
* xor
* nand
* implies
* nor

2. By the method of case analysis prove that at least two of your programs are
correct with respect to your truth table definitions, i.e., that they produce the
outputs specified by the truth tables for the given inputs.

3. What could still go wrong? Explain.

4. How many binary functions on booleans are there? Justify your answer. Hint:
think about the truth tables. The set of possible arguments is always the set of
pairs of booleans. How many different ways can these arguments be associated with
boolean results?
-/

/-
BOOLEAN ALGEBRA AS AN ALGEBRA
-/

/-
We have now gotten to the point where we can make sense of the term, boolean algebra.
Boolean algebra is an algebra, which is to say a set of values of a given type and a 
collection of operations closed on this set -- taking and returning values contained
in the set.

The set of values in the case of boolean algebra is the set containing the two truth
values, true and false, or T and F as we have called them here. The operations of 
boolean algebra include the operations that we have studied here, including the four
unary operations, the sixteen binary options, and so forth. Indeed, in a sense, this
file as a whole provides a computable definition of boolean algebra. It provides 
computable definitions of both the boolean type, comprising the set of two boolean 
values of type boolean, and a collection of unary and binary functions that are closed 
on this set.
-/

/-
SUMMARY

- types and values
- inductive definitions
- tuple values and tuple types
- relations and functions (set theoretic)
- functional programs
- proof strategies:
  * by simplification and reflexivity of equality
  * by exhaustive case analysis
- algebras
- case study: boolean algebra
  * inductive definition of the type of booleans
  * functions on booleans
  ** unary functions on booleans
  ** binary functions on booleans
  ** a ternary function: if then else (tbd)
-/
