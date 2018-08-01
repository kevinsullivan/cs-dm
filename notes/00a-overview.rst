*************
Overview/Plan
*************

* Read, write, and use classical first-order predicate logic to
  specify programs and enable tools to verify them automatically
* Learn set theory, diving into relations, as a case study in FOPL
* Learn language theory including specification and implementation of
  both language syntax and operational semantics, first for Boolean
  expressions, then bridging directly to propositional logic
* Explore satisfiability and the related concept of validity
* Get on the on-ramp to natural deduction
  - Meet, and for propositional logic, implement and validate, a
    catalog of proposed inference rules as principles of reasoning
  - Understand and implement, using our propositional logic validity
    checker, the notion of the *semantic* validity of such rules (by
    way of truth tables)
  - develop and implement a suite of classical valid and invalid
    inference rules, for all the non-quantifier-related introduction
    and elimination rules of natural deduction
  - Understand the concept of *semantic* entailment, why it can't
    scale, and that modern logic replaces semantic entailment with
    syntactic entailment
* Understand proofs as substitutes for semantic entailment checks
  - As compositions of inference rules grounded in the rules of
    natural deduction
  - Organized in layers of abstractions, where new rules are validated
    by proofs constructed using previously established results, again
    grounded in the core introduction and elimination rules of natural
    deduction
  - Learning to write code (in Lean) that construct proofs that are
    then typechecked for correctness
  - Learning how to apply type-guided top-down structured development
    to incrementally elaborate incomplete proofs initially with holes
  - Seeing that different kinds of propositions require corresponding
    kinds of proofs, and understanding how to select proof strategies
    at each level of a type-guided, top-down, structured development
* Introduction and elimination rules for the two basic quantifiers
  - dependent pairs for introducing/eliminating existential quantifiers
  - induction principles for introducing universal quantifiers
  - modus ponens as the elimination for for universal quantifiers
* Proof by induction
* Well founded recursion
  - structural recursion
  - co-induction
  - well-founded recursion



Students first learn to read, write, and use propositions in the
language of classical first-order predicate logic. They use this
language to write pre- and post-conditions, assertions, and loop
invariants for Java-like imperative code.

Next, to gain an understanding of a logic as a formal language with a
syntax and semantics, students undertake a systematic investigation of
*propositional* logic. They implement it. This is their introduction
to inductive type definitions for syntax and pattern matching and
structural recursion for operational semantics.

Having now learned (1) how to read, write, and apply classical
first-order predicate logic, and basic set theory in particular,
and (2) what a logic is and how to automate handling its syntax and
semantics,


