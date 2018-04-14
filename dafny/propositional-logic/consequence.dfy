include "decision.dfy"

module consequence
{
    import opened syntax
    import opened interpretation
    import opened evaluation
    import opened model
    import opened decision

    /*
    Deductive logical reasoning involves arguments of a very specific
    form, based on the idea that: if one is in a context in which a set
    of propositions (called "premises") are true, then it is necessarily 
    the case that another proposition, called a "conclusion", must also 
    be true."

    We represent such an argument in the form of what we will call an
    inference rule. An inference rule asserts that if each premise in a 
    given list of premises is true, then a given conclusion must also be
    true. We represent such an inference fule textually like this.
    
    [ list of premises ]
    --------------------  name_of_rule
          conclusion

    For example, the inference rule that we generally call "and introduction" (or "and_intro" for short) asserts that if we 
    know a proposition, P, is true, and we know that a proposition
    Q is true, then it must be that the proposition P /\ Q is also 
    true. Here's how we'd write this rule.

     P, Q
    ------  and_intro
    P /\ Q
              
    Valid inference rules, such as and_intro, provide us with powerful 
    means for logical reasoning. But not every proposed inference rule
    is valid. Here's an example. It's not that case in general that if
    (P implies Q) then (not P implies not Q). Here's how we'd write the
    invalid rule. 

     P -> Q
    --------  oops! wrong
    ~P -> ~Q

    For example, while it's true that "if it's raining outside the ground 
    is wet", that doesn't mean that "if the ground is wet then it must be raining outside." There might be other reasons for wet ground, such 
    as a sprinkler being turned on, snow melting, or a fire hydrant being
    running. This inference rule, then, is not valid.

    In this unit, we develop a suite of proposed inference rules and check
    each one for validity using our propositional logic validity checker.
    To check a rule, we convert it into an implication asserting that the
    conjunction of the premises implies the conclusion, and then we just
    check that proposition for validity by constructing a truth table for
    the proposition and checking that its true in every interpretation. 
    
    For example, we'd validate the and_intro rule by converting it into
    the proposition (P /\ Q) -> (P /\ Q). The left side is obtained by
    conjoining (joining with "and") the individual premises, P and Q. The
    right hand side is the conclusion. And it should be intuitive clear
    that the resulting proposition is always true; but if you're not 
    sure, just run our validity checker and check the truth table!

    Most of the inference rules we will propose will turn out to be valid.
    These end up being fundamental inference rules for deductive logic and
    proof, the topic of the next chapter of this course. A few of rules we
    propose will end up being not valid. These will capture common faulty
    forms of reasoning. Among the valid rules we will find two trace all
    the way back to Aristotle, namely syllogism and modus ponens. Here
    they are

    P -> Q, Q -> R
    --------------  syllogism
        P -> R

    This rule says that if from P you can deduce Q and if from Q you 
    can deduce R, then from P you can deduce R directly. Another way
    to state this rule is that implication is transitive! To check the
    validity of this rule, we will convert it into the implication,
    ((P -> Q) /\ (Q -> R)) -> (P -> R). Our grammar for propositional
    logic is entirely adequate to express this proposition, and our 
    validity checker will show it to be true under all interpretations.

    And here's modus ponens, also known as -> (arrow) elimination. 

    P -> Q, P
    --------- modus ponens (-> elimination)
        Q

    It says that if you know it's true that from P you can deduce Q, and 
    if you also know that P is true, then you can  deuce that Q must be 
    true. To check it's validity, we'd convert this inference rule into
    the proposition ((P -> Q) /\ P) -> Q), and submit this proposition 
    to our truth-table based validity checker (which does confirm its
    validity).

    This unit of the course elaborates and explores these ideas in the
    style of the course so far: by developing an implementation of the concepts, both to provide a precise and runnable explanation of the
    ideas, and to  enable hands on exploration and experimentation.

    The main content of this course module is in the consequence_test
    file, in the form of an organized suite of inference rules along
    with checks of their validity. Compile and run the program to see
    wat it does. 
    
    Most of the work required to implement its functionality was already 
    done to implement satisfiability, unsatisfiability, and validity 
    checking of arbitrary propositions. The only substantial new function
    needed for this unit was representing inference rules, converting
    them into propositional logic propositions, and formatting them for
    nice output. These functions are all implemented in this file. The 
    rest of this file. So let's get to it and see how it all works. 
    
    In this unit, we just introduce a simple new type, representing an
    inference rule as a pair, where the first element is itself a pair,
    namely a list of propositions (premises), and the second element is
    a proposition (conclusion), and where the second element of the pair
    is just a string giving a name to the inference rule. 
    */

    /************ IMPLEMENTATION FOLLOWS *****************/

    /*
    In the field of logic and proof, the term "context" generally 
    refers to a set of propositions that are already judged or assumed 
    to be true. Such propositions, called "premises", are then taken 
    as a basis for reasoning about the truth of another proposition, 
    referred to as a "conclusion". An inference rule is *valid* if
    the conclusion necessarily follows from the conjunction of the
    premises.
    
    We represent a context as a sequence of propositions (seq<prop>). 
    We assign the type name "context" as an "alias" for seq<prop>. In 
    the rest of this code, the type, context, thus means seq<prop>. A 
    modern logical reasoning system would represent context not as a 
    list but as a multiset (bag) of propositions, but for our purposes
    here, a list is just fine.
    */
    type context = seq<prop>


    /*
    With a representation of a context in hand, we new
    specify a representation for an inference rule as a
    named context/conclusion pair. We represent a rule as 
    pair within a pair, of type ((context,prop),string). 
    The first element is itself a pair: a context, which is 
    to say a list of propositions, and a conclusion, which
    is to say another proposition. The second element is a 
    string giving a name to the rule. That's it. We define 
    "inference_rule" as a type alias (a shorthand) for this 
    type. We then define nicely named functions for getting 
    the values of the fields of objects of this type. 
    */
    type inference_rule = ((context, prop), string)

    /*
    For code readability we provide nicely named functions
    for projecting (getting) the fields of an inference_rule
    triple. Recall that fields of a tuple are accessed using
    the notation r.0, r.1, etc., to get the first, second,
    etc. fields of a tuple, r. In this case, for example,
    r.0 is the context/conclusion pair within a rule pair, 
    r; and r.0.0 is the context (list of propositions) in
    that inner pair.
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
    The Main() routine of this unit, in consequence_test.dfy,
    mainly prints out a bunch of proposed inference rules along
    with indications of whether they are logically valid or not.
    This is the main routine for printing the outputs for the
    individual rules.  Compare the output produced when Main()
    runs, with this code, to see the correspondence. Then read
    the functions and methods that this method calls, most of
    which are just further down in this file, to see how this
    method is implemented. 
    */
    method checkAndShowInferenceRule(r: inference_rule)
    {
        // first check to see if r is logically valid
        var valid := isValid(r);

        // now get a printable string and width information for the rule
        var rule, width, width_with_name := showInferenceRule(r);

        // generate the right string to indicate validity or not
        var vmsg := "[" + (if valid then "Valid" else "Not Valid") + "]";

        // formatting: center the validty string within a ***string***
        vmsg := center(vmsg, width_with_name, '*');

        // print it all out across multiple formatted lines
        print vmsg + "\n\n" + 
              rule + "\n\n" +
              make_line('*', width_with_name) + 
              "\n\n\n";
    }


    /*
    This method returns a Boolean value indicating wether
    a given inference rule is semantically valid or not. 
    It does this by (1)  conjoining all the premises (a
    list of propositions) into a single proposition; (2) 
    forming an implication proposition stating that the "and"
    of all the premises implies the conclusion; (3) by then
    then checking to determine whether this implication is 
    logically valid; and (4) returning the result as a bool.
    */
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

    /*
    This is the routine that takes a context, i.e., a list of
    propositions, and turns it into one big conjunction. E.g.,
    given the context, [P1, P2, P3], it returns the proposition
    pAnd(P1(pAnd(P2,(pAnd(P3, pTrue))). This routine works by
    recursion. The base case, for the empty list of premises, 
    is just pTrue. Otherwise it returns the conjunction of the
    first premise in the list with the recursively computed
    conjunction of the rest of the premises in the list. The
    recursion terminates with the empty list, which always
    produces a pTrue as the last conjunct in the generated
    proposition. If you're not clear about the notation,
    premises[1..], please review the Dafny programming notes
    on sequences. (It means the sublist starting from the 
    second element, at index 1, to the end of the list).
    */
    function method conjoinPremises(premises: seq<prop>): prop
    {
        if |premises|==0 then pTrue
        else pAnd(premises[0], conjoinPremises(premises[1..]))
    }

    /*
    Return a string representation of an inference rule.
    This code gets strings representing the context, the
    conclusion, a line of the right length to separate them,
    and the name of the rule; it then computes strings for
    the context and conclusion centered above and/or below
    the line; and it finally prints the rule with its name
    to the right.
    */
    method showInferenceRule(r: inference_rule) 
        returns (rule_str: string, rule_width: nat, width_with_name: nat)
    {
        var context := showPropList(get_context(r));
        var concl := showProp(get_conclusion(r));
        var width := max(|context|,|concl|);
        context := center(context, width, ' ');
        concl := center(concl, width, ' ');
        var name := get_name(r);
        var line := make_line('-',width);
        rule_str := 
            context + "\n" +
            line + " " + name + "\n" +
            concl;
        return rule_str, width, width + 1 + |name|;
    }


    // Return the maximum of two natural numbers
    function method max(n: nat, m: nat): nat { if n > m then n else m } 

    // return a string centered in space of given width
    method center(s: string, w: nat, c: char) returns (result: string)
    {
        var left_gap := 
            if w > |s| 
            then (w - |s|) / 2
            else 0;
        var left_fill := make_line(c, left_gap);
        var right_fill_len := 
            if |left_fill| + |s| < w then w - (|left_fill| + |s|) else 0; 
        var right_fill := make_line(c, right_fill_len);
        return left_fill + s + right_fill;
    }

    /* 
    Return a string of characters of given width
    */
    function method make_line(c: char, width: nat): string
    {
        if (width==0) then "" else [c] + make_line(c, width-1)
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