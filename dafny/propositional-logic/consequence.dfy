include "decision.dfy"

module consequence
{
    import opened syntax
    import opened interpretation
    import opened evaluation
    import opened model
    import opened decision

    /*
    In the area of logical reasoning, the term "context" refers to a 
    set of propositions that is already judged or assumed to be true, 
    for use in reasoning about the truth of a follow-on proposition.
    The goal is generally to show that "in the context of a set of zero
    or more assumptions (the "context"), some conclusion must be true."
    We represent a context as a sequence of propositions, and give this
    type the name/synonmy context. A more complete implementation of
    logic would represent context as a multiset (bag) of propositions. 
    */
    type context = seq<prop>

    /*
    An inference rule is a named context/conclusion pair. 
    We represent an inference rule as a Dafny pair. The 
    first element is itself a pair: a context, which is 
    to say a list of propositions, and a conclusion, which
    is to say another proposition. The second element of 
    an inference rule is a string representing the name of 
    the rule. We define inference_rule as a type alias for 
    this structure, and then three functions for getting 
    the values of the fields.
    */
    type inference_rule = ((context, prop), string)

    /*
    For code readability we provide nicely named functions
    for projecting (getting) the fields of an inference_rule
    triple.
    */

    function method get_context(r: inference_rule): context 
    {
        r.0.0
    }

    function method get_conclusion(r: inference_rule): prop
    {
        r.0.1
    }

    function method get_name(r: inference_rule): string
    {
        r.1
    }


    /*
    This method returns a Boolean value indicating wether
    a given inference rule is semantically valid or not. 
    It does this by first conjoining all the premises (a
    list of propositions) into a single proposition; then 
    forming the overall proposition stating that the "and"
    of all the premises implies the conclusion; and finally
    by then checking to determine whether this implication 
    is logically valid, and returning the result as a bool.
    */
    method isValidRule(r: inference_rule) returns (validity: bool)
    {
        var premise := conjoinPremises(get_context(r)); 
        var implication := pImpl(premise,get_conclusion(r)); 
        var isValid, counter_examples := valid(implication);
        return isValid;
    }

    /*
    Given a list of propositions, return their conjunction. E.g.,
    given [P1, P2, P3], return pAnd(P1(pAnd(P2,(pAnd(P3, pTrue))).
    Note that the recursion ends with the empty list of premises
    yielding the proposition, pTrue. If the whole list of premises 
    really was empty (not just at the end of a recursion), this is 
    the right proposition to use, in that the resulting implication 
    would just say, "In any case at all, not conditioned on any other
    propositions being true, the conclusion is true." 
    */
    function method conjoinPremises(premises: seq<prop>): prop
    {
        if |premises|==0 then pTrue
        else pAnd(premises[0], conjoinPremises(premises[1..]))
    }

    /*
    Determine if sequent is semantically valid and print/show 
    it with either either a |= or !|= symbol accordingly, using
    lower-level routines to print constituent propositions.

    FIX: Rather than printing, should return string to be printed.
    */
    method checkAndShowInferenceRule(r: inference_rule)
    {
        var rule := showInferenceRule(r);
        var valid := isValidRule(r);
        print rule + "\n\n";
        var valid_msg := 
            if (valid) 
            then "This rule is valid" 
            else "This rule is not valid";
        print valid_msg  + "\n\n\n";
    }

    /*
    Return a string representation of an inference rule.
    */
    method showInferenceRule(r: inference_rule) returns (result: string)
    {
        
        var context := showPropList(get_context(r)); 
        var conclusion := showProp(get_conclusion(r));
        var line_len := max(|context|,|conclusion|);
        var line := make_line(line_len); 
        var center_context := center(context, line_len);
        var center_conclusion := center(conclusion, line_len);
        var name := get_name(r);
        result := 
            center_context + "\n" +
            line + " " + name + "\n" +
            center_conclusion;
    }

    // Return the maximum of two natural numbers
    function method max(n: nat, m: nat): nat { if n > m then n else m } 

    // return a string centered in space of given width
    method center(s: string, w: nat) returns (result: string)
    {
        var left_gap := 
            if w > |s| 
            then (w - |s|) / 2
            else 0;
        var left_fill := fill(' ', left_gap);
        return left_fill + s;
    }

    function method fill(c: char, width: nat): string
    {
        if (width==0) then "" else [c] + fill(c, width-1)
    }

    /* 
    Return a string of dashes (a "line") of length n
    */
    function method make_line(n: nat) : string
    {
        if (n==0) then "" else "-" + make_line(n-1)
    }


    /*
    Returns printable string rendering of a context
    for human reading. Format is a comma-separated 
    textual list of propositions, each serilized by
    the showProp method.

    Fix: Simplify name to showContext.
    */
    method showPropList(cx: context) returns (f: string)
    {
        var i := 0;
        var s: string := "";
        while (i < |cx|)
        {
            var s' := showProp(cx[i]);
            s := s + s';
            if (i < | cx | - 1 ) { s := s + ", "; }
            i := i + 1;
        }
        return s;
    }
}