/-
Every well formed term in Lean has a type.

Every type in Lean is, by definition, an expression of type Sort u for
some universe level u.

An expression of type, Sort u, is of type Sort (u + 1).

Prop abbreviates Sort 0. Type abbreviates Sort 1.

We say “α is a type” to express α : Type u for some u, and we say “p
is a proposition” to express p : Prop. Using the propositions as types
correspondence, given p : Prop, we refer to an expression t : p as a
proof of p. In contrast, given α : Type u for some u and t : α, we
sometimes refer to t as data.

When the expression β in Π x : α, β does not depend on x, it can be
written α → β. As usual, the variable x is bound in Π x : α, β, λ x :
α, t, and let x := t in s. The expression ∀ x : α, β is alternative
syntax for Π x : α, β, and is intended to be used when β is a
proposition. An underscore can be used to generate an internal
variable in a binder, as in λ _ : α, t.


variable (p: Prop)
variables (q r s: Prop)

(x : α) : an explicit argument of type α

{x : α} : an implicit argument, eagerly inserted

What makes simple type theory powerful is that one can build new types
out of others. For example, if α and β are types, α → β denotes the
type of functions from α to β, and α × β denotes the cartesian
product, that is, the type of ordered pairs consisting of an element
of α paired with an element of β.

Let us dispense with some basic syntax. You can enter the unicode
arrow → by typing \to or \r. You can also use the ASCII alternative
->, so that the expression nat -> nat and nat → nat mean the same
thing.  Both expressions denote the type of functions that take a
natural number as input and return a natural number as output. The
symbol N is alternative unicode notation for nat; you can enter it by
typing \nat.  The unicode symbol × for the cartesian product is
entered \times. We will generally use lower-case greek letters like α,
β, and γ to range over types. You can enter these particular ones with
\a, \b, and \g.

When writing type expressions, arrows associate to the right; for
example, the type of g is nat → (nat → nat). In type theory, this is
generally more convenient than writing g as a function that takes a
pair of natural numbers as input, and returns a natural number as
output. F

The command #reduce tells Lean to evaluate an expression by reducing
it to normal form, which is to say, carrying out all the computational
reductions that are sanctioned by the underlying logic. The process of
simplifying an expression (λ x, t)s to t[s/x] – that is, t with s
substituted for the variable x – is known as beta reduction, and two
terms that beta reduce to a common term are called beta
equivalent. But the #reduce command carries out other forms of
reduction as well:

this is an important feature of dependent type theory: every term has
a computational behavior, and supports a notion of reduction, or
normalization. In principle, two terms that reduce to the same value
are called definitionally equal. They are considered “the same” by the
underlying logical framework, and Lean does its best to recognize and
support these identifications.

Declaring constants in the Lean environment is a good way to postulate
new objects to experiment with, but most of the time what we really
want to do is define objects in Lean and prove things about them. The
def command provides one important way of defining new objects.

, Lean tags proofs as irreducible, which serves as a hint to the
parser (more precisely, the elaborator) that there is generally no
need to unfold it when processing a file. In fact, Lean is generally
able to process and check proofs in parallel, since assessing the
correctness of one proof does not require knowing the details of
another.

the axiom command is alternative syntax for constant. Declaring a
“constant” hp : p is tantamount to declaring that p is true, as
witnessed by hp

The symbol ∀ is alternate syntax for Π (Pi type)

• -reduction : An expression ( x, t) s -reduces to t[s/x], that is, the result of replacing x by s
in t.
• -reduction : An expression let x := s in t -reduces to t[s/x].
• -reduction : If c is a defined constant with definition t, then c -reduces to to t.
• -reduction : When a function defined by recursion on an inductive type is applied to an element given
by an explicit constructor, the result -reduces to the specified function value, as described in Section
4.4.

• -equivalence : An expression (x, t x) is -equivalent to t, assuming x does not occur in t.
• proof irrelevance : If p : Prop, s : p, and t : p, then s and t are considered to be equivalent.

  • #reduce t : use the kernel type-checking procedures to carry out reductions on t until no more
reductions are possible, and show the result
• #eval t : evaluate t using a fast bytecode evaluator, and show the result

  Lean provides ways of adding new objects to the environment. The following provide straightforward ways
of declaring new objects:
• constant c :  : declares a constant named c of type , where c is a declaration name.
• axiom c :  : alternative syntax for constant
• def c :  := t : defines c to denote t, which should have type .
• theorem c : p := t : similar to def, but intended to be used when p is a proposition.
• lemma c : p := t : alternative syntax for theorem
It is sometimes useful to be able to simulate a definition or theorem without naming it or adding it to the
environment.
• example :  := t : elaborates t and checks that it has sort  (often a proposition), without adding
it to the environment.
constant and axiom have plural versions, constants and axioms.
In def, the type ( or p, respectively) can be omitted when it can be inferred by Lean. Constants declared
with theorem or lemma are marked as irreducible.
Any of def, theorem, lemma, or example can take a list of arguments (that is, a context) before the colon. If
(a : ) is a context, the definition def foo (a : ) :  := t is interpreted as def foo :  a : ,
 :=  a : , t. Similarly, a theorem theorem foo (a : ) : p := t is interpreted as theorem foo
: 8 a : , p := assume a : , t. (Remember that 8 is syntactic sugar for , and assume is syntactic
sugar for .)

Syntactic sugar is provided for writing structured proof terms (3.6 refman):
• assume h : p, t is sugar for  h : p, t
• have h : p, from s, t is sugar for ( h : p, t) s
• suffices h : p, from s, t is sugar for ( h : p, s) t
• show p, t is sugar for (t : p)
-/
