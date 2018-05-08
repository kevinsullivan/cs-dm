*****************
Natural Deduction
*****************

Deductive logical reasoning involves arguments of a very specific
form, based on the idea that: if one is in a context in which a set of
propositions (called "premises") are true, then it is necessarily the
case that another proposition, called a "conclusion", must also be
true."


Named Inference Rules and Syntactic Entailment
==============================================

We represent such an argument in the form of what we will call an
inference rule. An inference rule asserts that if each premise in a
given list of premises is true, then a given conclusion must also be
true. We represent such an inference fule textually like this.
    
    [ list of premises ]
    --------------------  name_of_rule
          conclusion

Above the line is the context: a list of premises. Below the line is
the conclusion. To the right of this context/conclusion pair is a name
for the rule.
    
For example, the inference rule that we generally call "and
introduction" (or "and_intro" for short) asserts this: if we know a
proposition, P, is true, and we know that a proposition Q is true,
then it must be that the proposition P /\ Q is also true. Here's how
we'd write this rule.

     P, Q
    ------  and_intro
    P /\ Q
              
Valid inference rules, such as and_intro, provide us with powerful
means for logical reasoning. But not every proposed inference rule is
valid. Here's an example. It's not that case in general that if P
implies Q (the context) then not P implies not Q, the conclusion.
Thus is such a classic example of an invalid form of reasoning that
logicians have given it a name: denying the antecedent. (Antecedent is
another name for premise.) Here's how we'd write this bad rule.

     P -> Q
    --------  deny_antecedent
    ~P -> ~Q

Consider sn example of this for of reasoning to understand that it's
not valid. While it's true that "if it's raining outside the ground is
wet", that doesn't mean that "if the ground is wet then it must be
raining outside." There might be other reasons for wet ground, such as
a sprinkler being turned on, snow melting, or a fire hydrant being
running. This inference rule does not constutute an always-valid form
of deductive reasoning.

In this unit, we develop a suite of proposed inference rules and check
each one for validity using our propositional logic validity checker.
To check a rule, we convert it into an implication asserting that the
conjunction of the premises implies the conclusion, and then we just
check that proposition for validity using the methods we have already
developed: namely by constructing a truth table and checking that the
proposition is true in each of its possible interpretations.
    
For example, we'd validate the and_intro rule by converting it into
the proposition (P /\ Q) -> (P /\ Q). The left side (the premise) is
obtained by conjoining the individual premises, P and Q, yielding P
/\ Q. The right hand side is just the conclusion. And it should be
clear that the resulting proposition, which just says that P /\ Q
implies itself (i.e., that P /\ Q is true whenever P /\ Q is true) is
always true. If you're not convinced, represent the congoined
proposition, run our validity checker, and check the truth table!

Most of the inference rules we will propose will turn out to be valid.
These end up being fundamental inference rules for deductive logic and
proof, the topic of the next chapter of this course. A few of rules we
propose will end up being not valid. These will capture common faulty
forms of reasoning.

Aristotle's Logic
=================

Among the valid rules, two important ones originated with Aristotle:
syllogism and modus ponens. Here they are

    P -> Q, Q -> R
    --------------  syllogism
        P -> R

This rule says that if from P you can deduce Q and if from Q you can
deduce R, then from P you can deduce R directly. Another way to state
this rule is that implication is transitive! To check the validity of
this rule using truth tables, we convert it into the implication, ((P
-> Q) /\ (Q -> R)) -> (P -> R). Our syntax is adequate to express it,
and our validity checker will show it to be true under all
interpretations.

And here's modus ponens, also known as -> (arrow) elimination. 

    P -> Q, P
    --------- modus ponens (-> elimination)
        Q

It says that if you know it's true that from P you can deduce Q, and
if you also know that P is true, then you can deuce that Q must be
true. To check it's validity, we'd convert this inference rule into
the proposition ((P -> Q) /\ P) -> Q), and submit this proposition to
our truth-table based validity checker (which does confirm its
validity).

This unit of the course elaborates and explores these ideas in the
style of the course so far: by developing an implementation of the
concepts, both to provide a precise and runnable explanation of the
ideas, and to enable hands on exploration and experimentation.

The main content of this course module is in the consequence_test
file, and in the consequence file that implements the new
functions. This file formulates an organized suite of inference rules
along with checks of their validity. Compile and run the program to
see wat it does.
    
Most of the work required to implement its functionality was already
done to implement satisfiability, unsatisfiability, and validity
checking of arbitrary propositions. The only substantial new function
needed for this unit was representing inference rules, converting them
into propositional logic propositions, and formatting them for nice
output. These functions are implemented in consequence.dfy. 
    
Context
=======

In the field of logic and proof, the term "context" generally refers
to a set of propositions that are already judged or assumed to be
true. Such propositions, called "premises", are then taken as a basis
for reasoning about the truth of another proposition, referred to as a
"conclusion". An inference rule is *valid* if the conclusion
necessarily follows from the conjunction of the premises.
    
We represent a context as a sequence of propositions (seq<prop>).  We
assign the type name "context" as an "alias" for seq<prop>. In the
rest of this code, the type, context, thus means seq<prop>. A modern
logical reasoning system would represent context not as a list but as
a multiset (bag) of propositions, but for our purposes here, a list is
just fine.

    type context = seq<prop>


Named Inference Rule
====================

With a representation of a context in hand, we new specify a
representation for an inference rule as a named context/conclusion
pair. We represent a rule as pair within a pair, of type
((context,prop),string).  The first element is itself a pair: a
context, which is to say a list of propositions, and a conclusion,
which is to say another proposition. The second element is a string
giving a name to the rule. That's it. We define "inference_rule" as a
type alias (a shorthand) for this type. We then define nicely named
functions for getting the values of the fields of objects of this
type.

    
    type inference_rule = ((context, prop), string)

For code readability we provide nicely named functions for projecting
(getting) the fields of an inference_rule triple. Recall that fields
of a tuple are accessed using the notation r.0, r.1, etc., to get the
first, second, etc. fields of a tuple, r. In this case, for example,
r.0 is the context/conclusion pair within a rule pair, r; and r.0.0 is
the context (list of propositions) in that inner pair.



Semantic Entailment
===================

This method returns a Boolean value indicating wether a given
inference rule is semantically valid or not.  It does this by (1)
conjoining all the premises (a list of propositions) into a single
proposition; (2) forming an implication proposition stating that the
"and" of all the premises implies the conclusion; (3) by then then
checking to determine whether this implication is logically valid;
and (4) returning the result as a bool.

    method isValid(r: inference_rule) returns (validity: bool)
    {
        // form the conjunction of the premises
        var conjoined_premises := conjoinPremises(get_context(r)); 
 
        // build the implication proposition: premises -> conclusion
        var implication := pImpl(conjoined_premises,get_conclusion(r)); 

        // check the validity of this implication using a truth table
        var isValid, counter_examples := valid(implication);

        // and return the answer (ignoring any counter-examples)
        return isValid;
    }

This is the routine that takes a context, i.e., a list of
propositions, and turns it into one big conjunction. E.g., given the
context, [P1, P2, P3], it returns the proposition
pAnd(P1(pAnd(P2,(pAnd(P3, pTrue))). This routine works by
recursion. The base case, for the empty list of premises, is just
pTrue. Otherwise it returns the conjunction of the first premise in
the list with the recursively computed conjunction of the rest of the
premises in the list. The recursion terminates with the empty list,
which always produces a pTrue as the last conjunct in the generated
proposition. If you're not clear about the notation, premises[1..],
please review the Dafny programming notes on sequences. (It means the
sublist starting from the second element, at index 1, to the end of
the list).

    function method conjoinPremises(premises: seq<prop>): prop
    {
        if |premises|==0 then pTrue
        else pAnd(premises[0], conjoinPremises(premises[1..]))
    }



Natural Deduction Inference Rules
=================================

Inference rules good for classical and constructive logic
---------------------------------------------------------
        
Most rules apply to both classical and constructive logic.
A few rules involving negation elimination are valid only
in classical logic, but at the cost of extractability. KS:
check and explain.

True and False Introduction and Elimination Rules
+++++++++++++++++++++++++++++++++++++++++++++++++

        // True Introduction
        var true_intro: inference_rule  := (([], pTrue), "true_intro");
        checkAndShowInferenceRule(true_intro);  


	// note to kevin: check with jeremy on this one
        var not_intro := (([pImpl(P,pFalse)],pNot(P)), "not__intro");
        checkAndShowInferenceRule(false_intro);

        var false_elim  := (([pFalse], P),              "false_elim");
        checkAndShowInferenceRule(false_elim);  


And Introduction and Elimination Rules
++++++++++++++++++++++++++++++++++++++

        var and_intro   := (([P, Q], pAnd(P,Q)),        "and_intro");
        checkAndShowInferenceRule(and_intro);  

        var and_elim_l  := (([pAnd(P, Q)], P),          "and_elim_l");
        checkAndShowInferenceRule(and_elim_l);  

        var and_elim_r  := (([pAnd(P, Q)], Q),          "and_elim_r");
        checkAndShowInferenceRule(and_elim_r);  

Or Introduction and Elimination Rules
+++++++++++++++++++++++++++++++++++++

        var or_intro_l  := (([P], pOr(P, Q)),           "or_intro_l");
        checkAndShowInferenceRule(or_intro_l);  

        var or_intro_r  := (([Q], pOr(P, Q)),           "or_intro_r");
        checkAndShowInferenceRule(or_intro_r);  

        var or_elim     := (([pOr(P,Q),pImpl(P,R), pImpl(Q,R)],R), "or_elim");
        checkAndShowInferenceRule(or_elim); 
 

Implication Rules
+++++++++++++++++

        var impl_elim   := (([pImpl(P, Q), P], Q), "impl_elim");
        checkAndShowInferenceRule(impl_elim);

        // impl_intro is a little harder to express: ([P] |= Q) |= (P -> Q)

Resolution Rules
++++++++++++++++

        // resolution rules of inference: used in many theorem provers
        var resolution   := (([pOr(P, Q), pOr(pNot(Q), R)], pOr(P, R)), "resolution");
        checkAndShowInferenceRule(resolution);

        var unit_resolution  := (([pOr(P,Q), pNot(Q)], P), "unit_resolution");
        checkAndShowInferenceRule(unit_resolution);


Aristotle's Rules
+++++++++++++++++


        // a few more valid and classically recognized rules of inference
        var syllogism    := (([pImpl(P, Q), pImpl(Q, R)], pImpl(P, R)), "syllogism");
        checkAndShowInferenceRule(syllogism);

        var modusTollens := (([pImpl(P, Q), pNot(Q)], pNot(P)), "modusTollens");
        checkAndShowInferenceRule(modusTollens);


Inference Rules Valid in Classical but Not in Constructive Logic
----------------------------------------------------------------

        // rules in classical but not intuitionistic (constructive) logic 
        var double_not_elim := (([pNot(pNot(P))], P), "double_not_elim");
        checkAndShowInferenceRule(double_not_elim); 

        var excluded_middle: inference_rule := (([],pOr(P, pNot(P))), "excluded_middle");
         checkAndShowInferenceRule(excluded_middle);          



Fallacious Inference Rules
--------------------------
    

        // now for the refutation of some logical fallacies
        var affirm_conseq  := (([pImpl(P, Q), Q], P), "affirm_consequence");
        checkAndShowInferenceRule(affirm_conseq);

        var affirm_disjunct := (([pOr(P,Q), P],pNot(Q)),"affirm_disjunct");
        checkAndShowInferenceRule(affirm_disjunct);  

        var deny_antecedent := (([pImpl(P,Q)],pImpl(pNot(P),pNot(Q))),"deny antecedent");
        checkAndShowInferenceRule(deny_antecedent);



Algebraic properties / identities
=================================



Now we assert and check major algebraic properties of our
operators. Because we do this for arbitrary propositions, P, Q, and R,
one can be assure that these properties hold no matter what P, Q, and
are actually mean in the real world (e.g., maybe P means, "CS is
massively awesome"; but it just doesn't matter).

        var and_commutes_theorem  := (([], 
                                pAnd(pImpl(pAnd(P,Q),pAnd(Q,P)),
                                     pImpl(pAnd(Q,P),pAnd(P,Q)))), 
                                "P and Q is equivalent to Q and P\n");
        // why is explicit type needed here?
        var or_commutes_theorem: named_sequent  := (([], 
                                pAnd(pImpl(pOr(P,Q),pOr(Q,P)),
                                     pImpl(pOr(Q,P),pOr(P,Q)))), 
                                "P or Q is equivalent to Q or P\n");


Exercises
=========

Represent and validate in Dafny:


\begin{enumerate}
\item associativity of and
\item associativity of or
\item double negation elimination (as equivalence)
\item contrapositive (P -> Q) <=> (~Q -> ~P)
\item implication elminiation (P -> Q) <=> ~P || Q
\item demorgan-and: ~(P /\ Q) <=> ~P \/ ~Q
\item demorgan-or: ~(P \/ Q) <=> ~P /\ ~Q
\item dist-and/or: P /\ (Q \/ R) <=> (P /\ Q) \/ (P /\ R)
\item dist-or/and: P \/ (Q /\ R) <=> (P \/ Q) /\ (P \/ R)
\end{enumerate}

	
