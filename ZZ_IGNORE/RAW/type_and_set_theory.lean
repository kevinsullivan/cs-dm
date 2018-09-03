/- ** Logical Foundations of Mathematics ** -/

/-
Modern mathematics is axiomatic. It's logical. It is
"founded" on mutually consistent axioms and inference
rules. 

There is however more than one way to establish the 
logical foundations of mathematics.

The most widely used axiomatic foundation comprises a
set of axioms that describes what it means to be a set,
and everything else then builds on the concept of sets.
The resulting theory is called "set theory." Set theory
is the most widely accepted and used logical foundation
for everyday mathematics.

The natural numbers for example can be "formalized" as
sets. Zero is represented by the empty set; one by the
set that contains only the empty set; two by the set
that contains that set; and so forth. 

The specific set theory foundation for ordinary
mathematics is known as Zermelo-Frankl Set Theory 
with the Axiom of Choice (often abbreviated as ZFC). 
The axioms of ZFC capture our "naïve" view of sets 
as collections of elements. It took much time and
great care, however, to craft a set of axioms that
are not self-contradicting. The original formulation
of set theory turned out to be inconsistent! 

(Does the set of all sets that do not contain 
themselves contain itself? If it does, then it 
doesn't, and if it doesn't then it does: a real 
inconsistency! In fact it was this problem that
led mathematicians to a much more careful notion
of what it means to be a set, as captured by the
axioms of ZFC.

As another example of an inconsistency, there's 
a word in the English language to describe words 
that describe themselves: autological. The antonym 
of autological is heterological. "Polysyllabic" is 
autological, but  "palindrome" is heterological. 
Is the word "heterological" heterological? If the 
word doesn't describe itself, then it is, but then 
the word would describe itself. So, yeah, English
is inconsistent in this sense.)

The axioms of ZFC are somewhat technical; we will 
not explore them in this class. What you might want
to remember is that if you want to prove even simple
mathematical proposition in a precise, fully formal 
way using ZFC, it is a complex and messy affair. 

In fact, it's so messy that most mathematicians trade
in rigorous but informal proofs. By informal 
proofs we mean mathematical arguments written in a 
stylized form of a natural language, such as English.
For example, a proof of 0 = 0 and 1 = 1 might read
like this: "To prove the proposition, which is a
conjunction, we need proofs of the two parts. The
first, 0 = 0, is proved by noting that equality is
a reflexive relation, and 1 = 1 is proved similarly.
Given that both conjuncts are so, then so is the
overall conjunction. So it is shown (QED in latin)."

Because machines aren't much good at figuring out what
natural language text means with mathematical precision, 
it's nearly impossible today for computers to check that
purported informal proofs are correct. Proof checking 
remains a demanding, mostly human, and social process. 

When a mathematician claims to have produced a proof
of a theorem of potential significance, other experts
come together (often as reviewers for journals to which
mathematical purported proofs are generally submitted 
for review and publication) to see if they can find 
any errors in reasoning. They often do! 

Such human proof checking has in some cases proved to 
be nearly intractable. For example, in 2012, Shinichi 
Mochizuki, a reclusive Japanse mathematician, quietly 
posted to the web a 500-page "putative" proof of a 
major mathematical conjecture (proposition for which
there is not yet a proof) in number theory and geometry.
If correct, it could revolutionize mathematics. Yet the 
work is so complex and unusual that the mathematical 
community even to this day has still been unable even 
to comprehend the overall concept, not to mention 
checking every last detail for subtle errors. 
-/

/- 
HOMEWORK: Read this article. https://www.sciencealert.com/nightmarish-500-page-math-proof-even-experts-can-t-understand-about-published-shinichi-mochizuki
-/

/-
An alternative foundation for mathematics (in particular
for what is called "constructive" mathematics) is available
in what is called "type theory." It's basically a different
(from ZFC) set of axioms and inference rules on which math 
can be based. Not surprisingly, types, rather than sets, are
a fundamental building block of mathematics in type theory.
Sets can be modeled, but they are not built in. 

From your high school math background, you probably 
already have a reasonable intuition for sets as collections
of values. A type also defines a set of values, and each
value in that set has that type. But whereas a value can be
in many sets, in type theory a value has exactly one type.
Whenever you see a value, or an expression that reduces to
a value, in type theory, it thus makes sense to ask the
question, what is its type? Every well formed expression
and value in a type theory has exactly one type. 

In Lean, we can ask the type of an expression (including
of a literal expression that directly denotes a value) by
using the check command. Hover your mouse over the #check
command. Note that ℕ is mathematical notation for "natural
number", the type of non-negative integers.
-/

-- The types of some literal expressions 
#check 0
#check "Hello"
#check tt

-- defining a binding of an identifier to a value
def foo := 0

-- The type of a variable expression
#check foo

-- The types of some more complex expressions
#check 1 + foo
#check "Hello " ++ "Logic!"
#check tt && ff

/-
Without getting into complicated details, it will suffice 
for now to say that proofs are much more tractable objects 
in type theory than in set theory. Type theory has thus 
emerged as an important framework for *automating* the 
handling of logic in both mathematics and computer science. 

For computer scientists, it is also the main foundation for
functional programming, the theory of programming languages, 
and for formal verification of software correctness, which
is vitally important when ultra-high levels of confidence 
in the correctness of code is required (e.g., for security). 

This very tool and language that you're using now, the Lean
prover, is based on type theory. It's am example of what's 
known in the business as a proof assistant. But you can just 
think of it for now as a really cool tool in which you can 
write both programs and logic, and that can help you to 
construct "manageable" proofs. Through the magic of type 
checking it then *automatically* determines whether a proof 
is valid for a given proposition.

This technology holds the promise of eventually changing
the way that code is written and verified, and even the way 
that mathematics work.
-/

