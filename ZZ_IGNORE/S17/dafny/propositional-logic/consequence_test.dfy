

include "consequence.dfy"

module consequence_test
{
    import opened variables
    import opened syntax
    import opened consequence

    method Main()
    {    
        // Define variables for use in the following code. 
        var Pvar: propVar := mkPropVar("P");
        var Qvar := mkPropVar("Q");
        var Rvar := mkPropVar("R");
    
        // Define corresponding variable expressions.
        var P: prop := pVar(Pvar); 
        var Q := pVar(Qvar);
        var R := pVar(Rvar);

 
        /*
        Inference rules for classical and constructive logic
        */
        
        // True Introduction
        var true_intro: inference_rule  := (([], pTrue), "true_intro");
        checkAndShowInferenceRule(true_intro);  


        var false_elim  := (([pFalse], P),              "false_elim");
        checkAndShowInferenceRule(false_elim);  

        var and_intro   := (([P, Q], pAnd(P,Q)),        "and_intro");
        checkAndShowInferenceRule(and_intro);  

        var and_elim_l  := (([pAnd(P, Q)], P),          "and_elim_l");
        checkAndShowInferenceRule(and_elim_l);  

        var and_elim_r  := (([pAnd(P, Q)], Q),          "and_elim_r");
        checkAndShowInferenceRule(and_elim_r);  

        var or_intro_l  := (([P], pOr(P, Q)),           "or_intro_l");
        checkAndShowInferenceRule(or_intro_l);  

        var or_intro_r  := (([Q], pOr(P, Q)),           "or_intro_r");
        checkAndShowInferenceRule(or_intro_r);  

        var or_elim     := (([pOr(P,Q),pImpl(P,R), pImpl(Q,R)],R), "or_elim");
        checkAndShowInferenceRule(or_elim); 
 
        var impl_elim   := (([pImpl(P, Q), P], Q), "impl_elim");
        checkAndShowInferenceRule(impl_elim);

        // impl_intro is a little harder to express: ([P] |= Q) |= (P -> Q)

        // resolution rules of inference: used in many theorem provers
        var resolution   := (([pOr(P, Q), pOr(pNot(Q), R)], pOr(P, R)), "resolution");
        checkAndShowInferenceRule(resolution);

        var unit_resolution  := (([pOr(P,Q), pNot(Q)], P), "unit_resolution");
        checkAndShowInferenceRule(unit_resolution);

        // a few more valid and classically recognized rules of inference
        var syllogism    := (([pImpl(P, Q), pImpl(Q, R)], pImpl(P, R)), "syllogism");
        checkAndShowInferenceRule(syllogism);

        var modusTollens := (([pImpl(P, Q), pNot(Q)], pNot(P)), "modusTollens");
        checkAndShowInferenceRule(modusTollens);

        // rules in classical but not intuitionistic (constructive) logic 
        var double_not_elim := (([pNot(pNot(P))], P), "double_not_elim");
        checkAndShowInferenceRule(double_not_elim); 

        var excluded_middle: inference_rule := (([],pOr(P, pNot(P))), "excluded_middle");
         checkAndShowInferenceRule(excluded_middle);          

        var false_intro := (([pImpl(P,pFalse)],pNot(P)), "false_intro");
        checkAndShowInferenceRule(false_intro);          
    

        // now for the refutation of some logical fallacies
        var affirm_conseq  := (([pImpl(P, Q), Q], P), "affirm_consequence");
        checkAndShowInferenceRule(affirm_conseq);

        var affirm_disjunct := (([pOr(P,Q), P],pNot(Q)),"affirm_disjunct");
        checkAndShowInferenceRule(affirm_disjunct);  

        var deny_antecedent := (([pImpl(P,Q)],pImpl(pNot(P),pNot(Q))),"deny antecedent");
        checkAndShowInferenceRule(deny_antecedent);

        /*
        Exam 2 consequence answers: intro and elim rules for equivalence (iff)
        */
        var iff_elim_l := (([pEquiv(P,Q)], pImpl(P,Q)),"iff_elim_l");
        checkAndShowInferenceRule(iff_elim_l);

        var iff_elim_r := (([pEquiv(P,Q)], pImpl(Q,P)),"iff_elim_r");
        checkAndShowInferenceRule(iff_elim_r);

        var iff_intro := (([pImpl(P,Q), pImpl(Q,P)], pEquiv(P,Q)),"iff_intro");
        checkAndShowInferenceRule(iff_intro);
    }
}
