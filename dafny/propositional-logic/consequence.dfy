include "decision.dfy"

module consequence
{
    import opened syntax
    import opened interpretation
    import opened evaluation
    import opened model
    import opened decision

    /*
    In the area of logical reasoning, the term "context" is generally
    used to refer to a set of propositions that is taken as true for the
    purposes of reasoning about the truth of a follow-on proposition.
    The goal is generally to show that "in the context of a set of zero
    or more assumptions (the "context") some conclusion must be true."
    We represent a context as a sequence of propositions, and give this
    type the name/synonmy pContext. 
    */

    type context = seq<prop>
    type sequent = (seq<prop>, prop)

    method checkAndShowSequent(sq: sequent, name: string, lbl: bool)
    {
        var valid := checkSequent(sq);
        var msg := showSequent(sq, valid);
        print msg;
        if lbl { print "      " + name; }

    }
    method checkSequent(sq: sequent) returns (valid: bool)
    {
        var cx := sq.0;
        var conc := sq.1;
        valid := isConsequence(cx, conc);
        return;
    }

    method showSequent(sq: sequent, valid: bool) returns (r: string)
    {
        var cxstr := showPContext(sq.0);
        var cnstr := showProp(sq.1);
        r := cxstr // no space after empty sequent
            + (if |sq.0| > 0 then " " else "") 
            + (if valid then "|= " else "!|= ") + cnstr;
    }

    method isConsequence(cx: context, conclusion: prop) returns (r: bool)
    {
        var premise := conjoinPremises(cx);
        var implication := pImpl(premise,conclusion);
        var validity, counters := valid(implication);
        return validity;
    }

    /*
    Given a list of propositions, return their conjunction. E.g.,
    given [P1, P2, P3], return pAnd(P1(pAnd(P2,(pAnd(P3, pTrue))).
    Note that the recursion ends with the empty list of premises
    being equated to pTrue. pTrue is the "identity element" when it 
    comes to *evaluating* a conjunction of other propositions, so it
    is the right value to use in that sense. And if the whole list 
    of premises really was empty (not just at the end of a recursion),
    it is still the right value, in that the resulting implication 
    would just say, "In any case at all, not conditioned on any other
    propositions being true, the conclusion is true." 
    */
    function method conjoinPremises(premises: seq<prop>): prop
    {
        if |premises|==0 then pTrue
        else pAnd(premises[0], conjoinPremises(premises[1..]))
    }

    /*
    Returns printable string deserializing cx for humans
    */
    method showPContext(cx: context) returns (f: string)
    {
        var i := 0;
        var s: string := "";
//        s := "[";
        while (i < |cx|)
        {
            var s' := showProp(cx[i]);
            s := s + s';
            if (i < | cx | - 1 ) { s := s + ", "; }
            i := i + 1;
        }
        return s; // + "]";
    }
}