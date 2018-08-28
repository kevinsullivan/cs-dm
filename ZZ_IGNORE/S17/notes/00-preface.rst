*******
Preface
*******

This is a course in discrete mathematics (DM), particularly focused on
concepts of propositions and proofs, both in general and as they
relate to computing and software, in particular. The course is aimed
at early undergaduate students taking their second semester courses in
computer science, in preparation for majors in computer science or in
other disciplines that benefit from advanced skills in computing and
software development.

The usual DM course at this level is a paper-and-pencil affair about
proofs in classical first-order predicate logic. It teaches concepts
and methods that, anecdotally at least, many CS students find hard to
connect with their interests in computing.

This course introduces discrete math first through its application to
the specification of programs and automated formal verification using
classical first-order predicate logic, and then in more general terms,
turning to higher-order constructive logic. All aspects of the course
involve the use of software tools that bring the notions of logic and
proof to life: Dafny for first-order predicate logic for specification
and verification, and Lean for explicit construction of proof objects
for Lean's higher-order constructive logic.

Concepts covered in this course include the following:

* Read, write, and use classical first-order predicate logic to
  specify programs in Dafny use Dafny to verify them automatically
* Learn set theory, diving into relations, as a case study in FOPL
* Learn language theory including specification and implementation of
  both language syntax and operational semantics, first for Boolean
  expressions, then bridging to propositional logic
* Explore satisfiability and the related concept of validity
* Get on the on-ramp to natural deduction
  - Meet, and for propositional logic, implement and validate, a catalog of proposed inference rules as principles of reasoning
  - Understand and implement, using our propositional logic validity checker, the notion of the *semantic* validity of such rules (by way of truth tables)
  - develop and implement a suite of classical valid and invalid inference rules, for all the non-quantifier-related introduction and elimination rules of natural deduction
  - Understand the concept of *semantic* entailment, why it can't scale, and that modern logic replaces semantic entailment with syntactic entailment
* Understand proofs as substitutes for semantic entailment checks
  - As compositions of inference rules grounded in the rules of natural deduction
  - Organized in layers of abstractions, where new rules are validated by proofs constructed using previously established results, again grounded in the core introduction and elimination rules of natural deduction
  - Learning to write code (in Lean) that construct proofs that are then typechecked for correctness
  - Learning how to apply type-guided top-down structured development to incrementally elaborate incomplete proofs initially with holes
  - Seeing that different kinds of propositions require corresponding kinds of proofs, and understanding how to select proof strategies at each level of a type-guided, top-down, structured development
* Introduction and elimination rules for the two basic quantifiers
  - dependent pairs for introducing/eliminating existential quantifiers
  - induction principles for introducing universal quantifiers
  - modus ponens as the elimination for for universal quantifiers
* Proof by induction
* Well founded recursion
  - structural recursion
  - co-induction
  - well-founded recursion


Design Rationale
================

Several premises underlie the design of this course. First, students
want to know up front why logical proposition and proofs are relevant,
and how they are demonstrably and powerfully useful, for the practice
of computer science. This course thus grounds a study of mathematical
logic in the needs of software specification and verification. The
central idea is that while *code* is the language of implementation,
mathematical logic is the language of specification, and proofs, in
particular, are the language of verification.

Second, students of computer science are awed and inspired by *what
machines can do* when properly instructed. Moreover, recent, rapid,
and ongoing advances in the integration of logic and computing have
put us at the threshold of a new era in which every undergraduate
student of programming can and should be required to have a firm and
principled grounding in modern, *tool-supported* formal specification
and verification techniques.

A central premise of this course is this that students can now, should
now, and will be inspired to, see how mathematical logic and proof can
be applied, automated, and used for mechanical checking of code using
modern program verification tools.

The limited aim of the first segment of this course is to familiarize
students with the language and uses of first-order predicate logic by
teaching them how to write pre-/post-condition specifications, logical
assertions, and loop invariants for code that can then be verified by
a tool. The first part of the course thus relieves them of the need to
understand proofs while showing the benefits of proof automation using
Dafny's SMT-based program verification engine and real-time checking in
the VS Code plugin for Dafny.

Third, the effective study of set theory, relational logic, order
theory, and related concepts relies on a reasonable degree of fluency
in first-order predicate logic. The study of these topics should thus
occur only after students have hadsome significant practice with the
language of predicate logic. That said, studying set theory and its
related concepts will provide significant additional practice with and
will deepen students' understanding of this language and its uses.

Furthermore, while the set and relational abstraction provided by most
industrial programming languages are conceptually compromised (what on
earth is a *hashmap*, for example), the Dafny libraries are very well
suited for teaching set theory. Dafny's finite *set* and infinite
*iset* types provide operations and notations that directly reflect
the corresponding mathematics. One write cardinalities, unions, set
comprehensions, quantified expressions, etc. with natural syntax and
semantics. Rather than learning set theory by paper-and-pencil,
students can now learn it through expressive code and the immediate
feedback produced by Dafny.

Third, the on-ramp to learning proof techniques is complex and often
under-taught. This course takes the view that students will benefit
from a step-by-step development of underlying principles.  This course
thus takes students through an evolving landscape of concepts that
follow one from another. For example, only after developeing fluency
in reading, writing, and using predicate logic, only then are students
asked what is a logic?

Further Progression
===================

This question leads to the notion of a formal language, with a syntax
and semantics, and the idea that logics are such formal languages. As
an easy warm-up, students learn how to specify the syntax of a simple
variant of the language of Boolean expressions (with both literals and
connectives but no variables) using *inductive type definitions*; and
to specify and implement the semantics of a language using *pattern
matching* and *structural recursion* over terms of the language.

In the next chapter, students extend this language to support Boolean
variables, leading to the concept of an environment or interpretation:
a *state* in which an expression with variables is evaluated.

From there it's just a simple observation that the students have
actually constructed a language isomorphic to propositional logic.

Satisfiability and Validity
===========================

The concepts of models and of satisfiability (there exists a model),
of validity (for all models), and of unsatisfiability (there does not
exist a model) all follow directly. The class works through a basic
implementation of a SAT solver and validity/unsatisfiability checker
using truth tables.

Next, leveraging the same code base, students work through the concept
and implementation of *named inference rules* for *natural deduction*
for propositional logic, using our validity checker to test whether
proposed *reasoning principles* (inference rules) are valid or not.
They are thus led to the concept of *semantic entailment*. The also
see that it cannot scale because truth tables are exponential in the
number of variables in a given proposition. Incidentally, the coding
of these capabilities provides students with more and deeper examples
of the uses of specifications to write and check clean, correct code.

Syntactic Entailment
====================

Next, students are led to the notions of *syntactic entailment*, and
thus of *derivations* and *proofs*. At this point, the course finally
"surfaces" proof objects, and does so by changing tools from Dafny to
Lean, a new constructive logic proof assistant that, like Dafny, was
(and continues to be) developed at Microsoft Research (by Leo de
Moura). The introduction and elimination rules of natural deduction
are now recapitulated, but now in the context and language of
higher-order constructive logic.

Proof Strategies: A Type-Driven Approach
========================================

From there, proof strategies are taught as following in many cases
from the form of the proposition to be proved. Rather than initially
learning proofs as informal paper-and-pencil constructions, they see
them as precisely and inductively formed objects. The powerful type
system of Lean, which includes typed *holes* provides very beautiful
support for top-down structured development of proof objects, and,
indeed of programs, since programs are, of course, ultimately, also
proofs: of their types.

Theorems and Proofs
===================

Chapters follow on proof construction methods corresponding to the
various forms of propositions, eventually reaching dependent pairs for
existentially quantified propositions and proofs by induction for
universally quantified propositions. (Notes not yet in place: TBD).

Tools
=====

The course used the Dafny and Lean languages, and used VS Code and the
Dafny and Lean extensions for VS Code for essentially all student
work. Students worked on code in almost every class, generally pulling
updates to be discussed and worked on each day from the author's
evolving GitHub repository. Startin in Fall 2018 the plan is to
organize the repo as a set of branches, each introducing the
additional material for each day of the course.

The Dafny and Lean languages, per se, caused few complications. Dafny
has incomplete heuristics that lead to mystifying results in a few
cases. Notably, while it has heuristics that infer that intersections
of finite sets are finite, the same is not true for unions, so Dafny
rejects the obvious definition of set union as not well formed; and
this is but one example of family of related inferencing deficiencies.
In practice, students accepted that these are problems that could in
principle be resolved but that haven't yet been addressed in this
cutting-edge software.

The VS Code extensions, on the other hand, worked, but had greater
deficiencies. They still need some work. The Dafny extension sometimes
produces voluminous error logging messages visible to the user. They
confuse and annoy users, who just learn to ignore them. Both the Dafny
and Lean extensions sometimes fail to update error indications (red
squiggly underlines indicating errors in code), even when the code is
corrected. This issue causes consternation, frustration, anger, even
sadness among students, until they learn the work-arounds. Instructors
considering using this curriculum should be aware of these issues with
the VS Code extensions. The author is happy to discuss them with other
instructors and investigators who might be interested.

Exercises
=========

Exercises are currently provided in some but not all chapters. This is
work that planned for completion by the start of Fall semester, 2018.


.. todo

   Add missing chapters

Acknowledgements
================

The design of this course owes a lot to many other researchers. It was
indirectly inspired by pedagogical works around Coq: Pierce's Software
Foundations and Chlipala's book, Certified Programming with Dependent
Types. Unlike those works, this course is geared to the beginning
undergraduate students. It aims to make no assumptions about prior
knowledge except of the basic constructs of imperative programming.

This course was also inspired and influenced by the *How to Design
Programs* curricula by Felleisen, Krishnamurthi, et al., as realized
in the *MOOC* courses by Kiczales.  Unlike those courses, this course
relies on strongly, statically typed languages that provide unified
support for code, logic, proof, and structured, top-down, type-driven
development of all of the above, through the incremental refinement of
typed holes in typed terms.

The author gratefully acknowledges the support of Rustan Leino, the
developer of Dafny, and several others who provided insight and help
in its use; Farhad Mehta, two of whose former undergraduate students
developed the VS Code extension; Leo de Moura, Tom Ball, and Jeremy
Avigad, for their help with Lean, and Jeremy for open source code that
taught the author how to format this book using Sphinx; Ken Birman for
suggesting that the author look at Dafny as a candidate for an early
course for computer science with formal underpinnings. The author also
thanks the students in his CS2102 Spring 2018 class for their patience
and attention learning discrete math in the style described here. For
many relevant conversations over the years, the author also thanks
Mattias Felleisen, Shriram Krishnamurthi, Gregor Kiczales, Mark
Guzdial and others for discussions about software-related pedagogy.

Feedback and Corrections
========================

The author advises that this book in its current form is still a very
rough draft. Corrections and other forms of feedback are welcomed. The
author requests that corrections in particular be posted as *issues*
on the author's GitHub repo, at http://github.com/kevinsullivan/cs-dm.
Feel free to follow up with email to sullivan.kevinj at gmail. At some
point soon the author will develop a protocol allowing members of the
broader community to contribute to this effort, perhaps in the style
of Pierce around Software Foundations. 

