******************
12. Satisfiability
******************

We can now characterize the most important *open question* (unsolved
mathematical problem) in computer science.  Is there an *efficient*
algorithm for determining whether any given Boolean formula is
satisfiable?

whether there is a combination of Boolean
variable values that makes any given Boolean expression true is the
most important unsolved problem in computer science. We currently do
not know of a solution that with runtime complexity that is better
than exponential the number of variables in an expression.  It's easy
to determine whether an assignment of values to variables does the
trick: just evaluate the expression with those values for the
variables. But *finding* such a combination today requires, for the
hardest of these problems, trying all :math:``2^n`` combinations of
Boolean values for *n* variables.

At the same time, we do not know that there is *not* a more efficient
algorithm. Many experts would bet that there isn't one, but until we
know for sure, there is a tantalizing possibility that someone someday
will find an *efficient decision procedure* for Boolean satisfiability.

To close this exploration of computational complexity theory, we'll
just note that we solved an instances of another related problem: not
only to determine whether there is at least one (whether *there
exists*) at least one combination of variable values that makes the
expression true, but further determining how many different ways there
are to do it.

Researchers and advanced practitioners of logic and computation
sometimes use the word *model* to refer to a combination of variable
values that makes an expression true. The problem of finding a Boolean
expression that *satisfies* a Boolean formula is thus somtetimes
called the *model finding* problem. By contrast, the problem of
determining how many ways there are to satisfy a Boolean expression is
called the *model counting* problem.

Solutions to these problems have a vast array of practical uses.  As
one still example, many logic puzzles can be represented as Boolean
expressions, and a model finder can be used to determine whether there
are any "solutions", if so, what one solution is. 


Interpretations for a Proposition
=================================


This method returns a sequence of all possible interpretations for a
given proposition. It does it by getting a sequence of all the
variables in the expression and by then calling a helper function,
truth_table_inputs_for_vars, which does most of the work.

.. code-block:: dafny
    
    method truth_table_inputs_for_prop(p: prop) 
        returns (result: seq<pInterpretation>)
        ensures forall v :: v in getVarsInProp(p) ==> 
                    forall i :: 0 <= i < |result| ==>
                        v in result[i];     // kjs
    {
        var vs := seqVarsInProp(p);
        result := truth_table_inputs_for_vars(vs);
    }
    


Interpretations for a Sequence of Propositions
==============================================

This method returns a sequence of all possible interpretations for a
given sequence of Boolean variables, in increasing order from all
false to all true. Each interpretation is a map from each of the
variables to that variable's bool value under the given
interpretation. In other words, this method returns the "input" parts
of each row of a truth table for the given propositional variables.

    
.. code-block:: dafny
    
    method truth_table_inputs_for_vars(vs: seq<propVar>) 
        returns (result: seq<pInterpretation>)
        ensures forall i :: 0 <= i < |result| ==>   // kjs
            forall v :: v in vs ==> v in result[i];
    {
        result := [];
        var interp := all_false_interp(vs);
        var i: nat := 0;
        var n := pow2(|vs|);
        while (i < n)
            invariant i <= n;
            invariant |result| == i;
            invariant forall v :: v in vs ==> v in interp;
            invariant 
                forall k :: 0 <= k < i ==> 
                    forall v :: v in vs ==>
                        v in result[k];


        {
            result := result + [interp];
            interp := next_interp(vs, interp);
            i := i + 1;
        }
    }
    



The All-False Interpetation
===========================


Return an interpretation for the variables in the sequence vs such
that every variable maps to false.


.. code-block:: dafny


    method all_false_interp(vs: seq<propVar>) 
        returns (result: pInterpretation)
        ensures forall v :: v in vs ==> v in result //kjs
    {
        result := map[];
        var i := 0; // the number of elements in the map so far
        while (i < | vs |)
            invariant i <= |vs|;
            invariant forall k :: 0 <= k < i ==> vs[k] in result;
        {
            result := result[ vs[i] := false ];
            i := i + 1;
        }
    }



HuH???
======


.. code-block:: dafny


    method truth_table_inputs_for_props(ps: seq<prop>) 
        returns (result: seq<pInterpretation>)
    {
        var vs := seqVarsInProps(ps);
        result := truth_table_inputs_for_vars(vs);
        return;
    }
    




Increment Interpretation
========================

Given a sequence of variables and an interpretation for those
variables, computes a "next" interpretation.  Treat the sequence of
values as a binary integer and increment it by one. Any variables in
vs that are not in interp are ignored. Would be better to enforce a
pre-condition to rule out this possibility.

.. code-block:: dafny


    method next_interp(vs: seq<propVar>, interp: pInterpretation) 
        returns (result: pInterpretation)
        requires forall v :: v in vs ==> v in interp;   //kjs
        ensures forall v :: v in vs ==> v in result;
    {
        result := interp;
        var i := | vs | - 1;
        while (i >= 0 ) 
            invariant forall v :: v in vs ==> v in result;  //kjs
        {
            if (interp[ vs[i] ] == false) 
            { 
                result := result[ vs[i] := true ];
                break; 
            } 
            else
            {
                result := result[ vs[i] := false ];
            }
            i := i - 1;
        }
    }



    

Print Truth Table for a Propositional Logic Proposition
=======================================================

.. code-block:: dafny


    method show_truth_table_for_prop(p: prop, ord: seq<propVar>, labels: bool)
        requires forall v :: v in getVarsInProp(p) ==> v in ord; // kjs
    {
        var varSeq := seqVarsInProp(p);
        var tt_inputs := truth_table_inputs_for_vars(varSeq);
        var i := 0;
        while (i < | tt_inputs |) 
        {
            show_interpretation(tt_inputs[i],ord,labels);
            print " :: ";
            var tt_input := tt_inputs[i];
            var out := pEval(p, tt_inputs[i]);
            var propString := showProp(p);
            if labels { print propString, " := "; }
            print out, "\n";
            i := i + 1;
        } 
    }
}



Utility Routine
===============

Compute and return 2^n given n.


.. code-block:: dafny


    function method pow2(n: nat): (r: nat)
        ensures r >= 1
    { 
        if n == 0 then 1 else 2 * pow2(n-1) 
    }



Models
------

This important method returns a sequence containing all (and only) the
models of the given proposition. It works by generating a sequence of
all possible interpretations for the variables in the proposition
(this is the purpose of truth_table_inputs), and by then passing these
interpretations, the proposition, and an empty list of models to the
helper function, which augments that empty list with each of the
interpretations for which the proposition evaluates to true.  */


.. code-block:: dafny


    method get_models(p: prop) returns 
        (r: seq<pInterpretation>)
    {
        var tt_inputs := truth_table_inputs_for_prop(p);
        r := get_models_helper (tt_inputs, p, []);
        return r;
        
    }

This method iterates through a list of interpretations and appends
each one, for which the given proposition, e, evaluates to true, to
the list, acc, which is then returned.


.. code-block:: dafny

   method get_models_helper(tt_inputs: seq<pInterpretation>, p: prop, acc: seq<pInterpretation>) 
        returns (r: seq<pInterpretation>)
        requires forall v :: v in getVarsInProp(p) ==> 
                    forall i :: 0 <= i < |tt_inputs| ==> 
                        v in tt_inputs[i];  // kjs -- need to import variables
    {
        var idx := 0;
        var res := acc;
        while (idx < | tt_inputs |)
        {
            if pEval(p, tt_inputs[idx]) 
            { res := res + [ tt_inputs[idx] ]; } 
            idx := idx + 1;
        }
        return res;
    }
}




Satisfiability, Unsatisfiability, Validity
------------------------------------------

Return true (and an empty interpretation) if the given Boolean
expression is valid, otherwise return false with a counter-example,
i.e., an interpretation for which the given expression is false.

.. code-block:: dafny


    method satisfiable(e: prop) returns (result: bool, 
                                         models: seq<pInterpretation>)
    {
        models := get_models(e);
        if | models | > 0 { return true, models; }
        return false, [];
    }

Return true (and an empty interpretation) if e is unsatisfiable,
otherwise return false and a counterexample, i.e., a model, i.e., an
interpretation, that makes the expression true.

.. code-block:: dafny

    method unsatisfiable(e: prop) 
        returns (result: bool, 
                 counters: seq<pInterpretation>)
    {
        var hasModels: bool;
        hasModels, counters := satisfiable(e);
        return !hasModels, counters;
    }

A proposition is valid if it's true under every interpretation. If
it's not valid, then there will be some interpretation under which
it's false. In this case, the negation of the proposition will be true
under that interpretation, and it will thus be a counterexample to the
claim that the proposition is valid. If such a "witness" to the
invalidity of the original proposition is found, return false to the
question of validity, along with the witnesses to invalidity.


.. code-block:: dafny

    method valid(e: prop) returns (result: bool, 
                                   counters: seq<pInterpretation>)
    {
        var negIsSat: bool; 
        negIsSat, counters := satisfiable(pNot(e));
        return !negIsSat, counters;
    }
 
Invalidity means there's a witness to the negation of the main
propositions, i.e., that the negation is satisfiable. Try to satisfy
it and return results and counterexamples (models of the negated prop)
accordingly.


.. code-block:: dafny

    method invalid(e: prop) returns (result: bool, 
                             counters: seq<pInterpretation>)
    {
        var negIsSat: bool; 
        negIsSat, counters := satisfiable(pNot(e));
        return negIsSat, counters;
    }
 }

