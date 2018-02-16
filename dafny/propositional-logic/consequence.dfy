include "decision.dfy"

module consequence
{
    import opened syntax
    import opened interpretation
    import opened semantics
    import opened model
    import opened decision

    type pContext = seq<pExp>

    method isConsequence(context: pContext, conclusion: pExp) returns (r: bool)
    {
        var premise := conjoinPremises(context);
        var implication := pImpl(premise,conclusion);
        var validity, counters := valid(implication);
        return validity;
    }

    /*
    Given a list of propositions, return their conjunction. E.g.,
    given [P1, P2, P3], return pAnd(P1(pAnd(P2,(pAnd(P3, pTrue))).
    To terminate the recursion, we throw in that extra pTrue as
    a last proposition in the resulting nested expression.
    */
    function method conjoinPremises(premises: seq<pExp>): pExp{
        if |premises|==0 then pTrue
        else pAnd(premises[0], conjoinPremises(premises[1..]))
    }

    method showPContext(cx: pContext) returns (f: string)
    {
        var i := 0;
        var s: string := "[";
        while (i < |cx|)
        {
            var s' := showPExp(cx[i]);
            s := s + s';
            if (i < | cx | - 1 ) { s := s + ", "; }
            i := i + 1;
        }
        return s + "]";
    }
}