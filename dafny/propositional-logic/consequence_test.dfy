

include "consequence.dfy"

module consequence_test
{
    import opened variables
    import opened syntax
    import opened consequence

    method Main()
    {    
        /*
        Set up data for testing. Note that in our
        design, variables, of type propVar, are *not*
        themselves propositions. Rather, they are basic
        data used to construct variable proposition
        expressions.

        It's easier to represent interpretations using
        polymorphic maps when "variables" objects have
        their own type, than when they are a subset of
        the terms of our proposition expressions type, 
        prop. 
        
        We might want to find a different name for them
        to make it clearer that they're not propositions.
        */

        // define three raw variables, enough for simple tests
        var Pvar: propVar := mkPropVar("P");
        var Qvar := mkPropVar("Q");
        var Rvar := mkPropVar("R");
    
        // define three propositional "variable expressions"
        var P: prop := pVar(Pvar); 
        var Q := pVar(Qvar);
        var R := pVar(Rvar);

        /*
        And now the main content of this unit: We propose and demonstrate
        the logic validity of a set of "logical inference rules", which you
        can think of as "always valid ways of deducing consequences from 
        given antecedents." 

        Key concepts:
        - inference rule: a principle for deriving conclusions (propositions)
        from lists of antecedents (propositions) that are already known to be,
        or that are at least assumed to be, true.
        
        - Forward and backwards reasoning. Reasoning in reverse, an inference rule 
        provides a method for breaking down the task of showing that a conclusion 
        is true by showing that the corresponding antecedents are true. Recursively 
        applying this technique until one gets to truths that are accepted without 
        antecedent conditions is a fundamental method of "proof engineering."

        - entailment: the idea that a conclusion follows from a set of antecedents
        
        - semantic entailment: checking the logical validity of an inference
        by the method of exhaustively checking truth tables for the corresponding
        proposition

        - the unscalability of reasoning semantically about complex propositions:
        how large is the truth table for a proposition with "n" variables? does it
        "scale" to check the truth of a given proposition for all combinations of
        variable values when the number of variables is large (let's say 1,000,000)

        - syntactic entailment: the ultimate target concept of this whole course.
        We can reason about the truth of a given proposition not by enumerating all
        possible interpretations and showing it's true under all of them, but by
        establishing a chain of inferences. That is, we take our *semantically*
        validated inference rules and apply them directly to construct what we 
        will call "derivations" or "proofs" that show that a given conclusion can
        be "shown to be true" by a chain (or more accurately a tree) of applications
        of validated inference rules with no need to go back to truth tables.
        */

        // *semantic* verification of soundness of ND rules of inference
        var true_intro  := (([], pTrue),"\t\t\t\tpTrue is true without conditions\n");
        var false_elim  := (([pFalse],P),"\t\t\t\tif pFalse is true, anything goes\n");


        var and_intro   := (([P, Q], pAnd(P,Q)),"\t\t\tand introduction; like constructor\n");
        var and_elim_l  := (([pAnd(P, Q)], P),"\t\t\t\tand elimination (get left)\n");
        var and_elim_r  := (([pAnd(P, Q)], Q),"\t\t\t\tand elimination (get right)\n");

        var or_intro_l  := (([P], pOr(P, Q)),"\t\t\t\tor intro, given truth of left arg\n");
        var or_intro_r  := (([Q], pOr(P, Q)),"\t\t\t\tor intro, given truth of right arg\n");
        var or_elim     := (([pOr(P,Q),pImpl(P,R), pImpl(Q,R)],R),"proof by cases\n");
 
        var impl_elim   := (([pImpl(P, Q), P], Q),"\t\t\t-> elimination (modus ponens)\n");
        // impl_intro is a little harder to express: ([P] |= Q) |= (P -> Q)
 
        // resolution rules of inference used in many theorem provers
        var resolution   := (([pOr(P, Q), pOr(pNot(Q), R)], pOr(P, R)),"\tresolution\n");
        var unit_resoln  := (([pOr(P,Q), pNot(Q)], P),"\t\t\tunit resolution\n");

        // rules valid in classical but not intuitionistic (constructive) logic 
        var double_not_elim := (([pNot(pNot(P))], P),"\t\t\tdouble negation elimination\n");
        var law_of_excluded_middle: named_sequent := (([],pOr(P, pNot(P))),"\t\t\tlaw of exluded middle\n");  // note: need explicit type declaration here
        var false_intro := (([pImpl(P,pFalse)],pNot(P)),"\t\tproof by contradiction\n");
    
        // a few more valid and classically recognized rules of inference
        var syllogism    := (([pImpl(P, Q), pImpl(Q, R)], pImpl(P, R)),"syllogism\n");
        var modusTollens := (([pImpl(P, Q), pNot(Q)], pNot(P)), "\t\tmodus tollens\n");

        // now for the refutation of some logical fallacies
        var affirm_conseq  := (([pImpl(P, Q), Q], P), "\t\t\tdon't affirm consequences!\n");
        var affirm_disjunct := (([pOr(P,Q), P],pNot(Q)),"don't affirm dijuncts!\n");
        var deny_antecedent := (([pImpl(P,Q)],pImpl(pNot(P),pNot(Q))),"don't deny  antecedents!\n");

        // And finally, identities (provable unconditionally, theorems) "COMING SOON"
        print "\n\n";
        checkAndShowSequent(true_intro);  
        checkAndShowSequent(false_elim);  
        checkAndShowSequent(and_intro);  
        checkAndShowSequent(and_elim_l);  
        checkAndShowSequent(and_elim_r);  
        checkAndShowSequent(or_intro_l);  
        checkAndShowSequent(or_intro_r);  
        checkAndShowSequent(or_elim);  
        checkAndShowSequent(false_intro);          
        checkAndShowSequent(double_not_elim); 
        checkAndShowSequent(law_of_excluded_middle); 
        checkAndShowSequent(syllogism);
        checkAndShowSequent(modusTollens);

        checkAndShowSequent(impl_elim);
        checkAndShowSequent(affirm_conseq);
        checkAndShowSequent(resolution);  
        checkAndShowSequent(unit_resoln);  
    }
}
