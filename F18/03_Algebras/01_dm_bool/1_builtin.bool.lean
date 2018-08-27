/- TYPES AND VALUES: Case study of the boolean type -/

/-
In Lean, Every value, and indeed every expression that represents some 
value, has exactly one type. A type in turn defines a set of values,
namely the set of all and the only values of the given type. 

For example, in Lean, the Boolean values, tt and ff (for "true" and "false")
are the two and only values of the type called bool. 

In Lean, you can always check the type of any expression, including any
literal value, by using the #check command. Hover your mouse pointer over 
the #check command to see its output.
-/

#check tt

/-
The output of this command is what we call a "type judgement". In
particular, it is the type judgement, "tt : bool." You can read this
as saying "the type of tt is bool".
-/

/-
EXERCISE: use #check to confirm that the type of ff is also bool.
-/

/- 
*** Operators and xpressions and their types
-/

/-
Through its libraries, Lean provides many operations on Boolean values.
These include the usual "and", "or", and "not" operators familiar from
CS1. For example, "band tt ff" is an expression in Lean that applies the
Boolean "and", or conjunction, operator to the Boolean values tt and ff 
to compute a new Boolean value. The or function in lean is called bor.
And the not function is called bnot.
-/

/-
The result of applying the bnot operator to one Boolean value is
another Boolean value. Thus the type of an expression in which the
bnot operator is applied to a Boolean value is ... wait for it ...
bool.
-/

#check bnot tt

/-
Note that functions are applied to values by writing the function
name followed by the argument(s) to the function.
-/

/-
The Boolean "and" (conjunction) and "or" (disjunction), operators
are called band and bor, respectively.  Eacof these functions
takes two Boolean-valued arguments and returns a result of type
bool.
-/

#check bor tt ff

/-
EXERCISE: Use #check to check the types of expressions in which
the band operator is applied to two Boolean arguments.
-/

/-
You will remember from CS1 that Boolean expressions are usually
written something like this: true && false, or true || false, 
where && means "and" and || means "or." From now on, you can
think of || and && as just shorthands for "and" and "or" with
the main difference being that they are written between rather
than in front of their arguments. Lean also provides the same
shortcutss.  We call operators such as band and bor "prefix",
because they are written before their operands, while && and
|| are called "infix" because they are written between their
arguments. There are no differences in meaning, just in the
"surface syntax." (band tt ff) and (tt && ff) mean exactly the
same thing. The Lean compiler really just converts the latter
into the former "under the hood."
-/

#check tt && ff

/-
EXERCISE: Check the type of the expression (bor tt ff) but now
write the expression using the || infix operator.
-/


/-
Lean also provides a mathematical shorthand for the Boolean not
operator. You get this notation in Lean by typing a backslash
immediately followed by "not" ane then a space.
-/

#check ¬ tt

/-
EXERCISE: type the same #check command to be sure you know how
to typeset the not operator in Lean. As you'll see, Lean gives
you the ability to write mathematical logic using ordinary math
and logic symbols.
-/

/- 
*** The Evaluation (or Reduction) of Expressions
-/

/-
Part of magic of computers is that they can tell you not
only the type of an expression, but even what value it 
reduces to when you evaluate the expressions. In Lean, 
you can use the #eval command to have Lean compute and
display the reduced value of an expression.
-/

#eval band tt ff

/-
EXERCISE: Use #eval to evaluate the disjunction of tt and ff.
EXERCISE: Use #eval to evaluate the negation of tt
EXERCISE: Evaluate a Lean expression for what we would 
informally say as "the negation of the conjunction of true
and false". Use parenthesis to group the and operator and its
arguments. Use #check to check the type of this expression,
and use #eval to reduce it to a Boolean value.
-/

/-
At this point, you should feel good! You have learned
about types, values, operators that are closed on values of a 
type, and expressions involving these operators and values. What 
you are seeing is the "algebra" of Boolean values, formalized in 
Lean, and amenable to automated type checking and evaluation.
-/

/-
Now it's one thing to use a computerize algebra built in to a
programming system, such as Lean or Python, that someone else has
given you, but it's another thing altogether to understand how to 
define an algebra yourself. Seeing how to do that is the purpose
of the next unit. And we might as well proceed by implementing
our own version of the Boolean algebra we just saw.
-/

