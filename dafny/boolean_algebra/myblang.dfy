module myblang
{

    /*
    VARIABLES: We want to define a language of Boolean expressions
    that includes Boolean variables, not just literals. So beyond
    being able to represent expressions such as (true && false), in
    our little language as (bAnd(bTrue,bFalse)), we also want to be
    able to write expressions such as (P && Q), or in our language
    as (bAnd(bVar(P),bVar(Q))). To this end, we need to define a new
    type, the values of which are "variables", and then we need a 
    way to incorporate *variable expressions* into the syntax of our
    language. 

    Here's a datatype with a single constructor, V, taking one nat
    as an argument. Terms such as V(0), V(1), and V(2) are thus of
    type "variable". These will be our variables.
    */

    datatype variable = V(n:nat)
    
    /*
    Note that we can give variables more convenient names in code
    by binding them as the values of better-named Dafny variables, 
    like this:
        var P := V(0);
        var Q := V(1);
        var R := V(2);
    */
    
    /*
    SYNTAX: Expresions are values of an inductively defined type
    */
    datatype bExp = 
        /*
        Here are the constructors for Boolean literal expressiosn
        */
        bTrue | 
        bFalse | 
        /*
        We now provide "bVar" as a constructor for building *variable*
        expressions.
        */
        bVar(v: variable) |

        /*
        And finally we provide constructors for building expressions
        with the usual Boolean connectives.
        */
        bNot(e: bExp) |
        bAnd(e1: bExp, e2: bExp) |
        bOr(e1:bExp, e2: bExp) |
        bImpl(e1: bExp, e2: bExp) |
        bIfThenElse(e1: bExp, e2: bExp, e3: bExp)


    /* 
    SEMANTICS: Their meaning is evaluated by structural recursion
    */
    function method bEval(e: bExp, env: map<variable,bool>): bool    
    {
        match e 
        {
            /*
            Here are the evaluation rules for literal and operator
            expressions (the latter using the Boolean connectives).
            You will note that the code as we wrote it in class does
            not typecheck. There are lots of red underlines. "DON'T
            PANIC. THINK!" The reason is that bEval now takes *two*
            parameters: an expression and an *environment* in which
            to evaluate the values of variables that appear in the
            expression. However, our original code continues to call
            bEval (recursively) with only one parameter. Clearly you
            must a provide a second parameter to each recursive call.
            The question is, in what environment should you evaluate
            the subexpressions! THINK HARD. You will eventually see
            the light. Don't give up.
            */
            case bTrue => true 
            case bFalse => false
            case bNot(e) => !bEval(e)
            case bAnd(e1, e2) => bEval(e1) && bEval(e2)
            case bOr(e1, e2) => bEval(e1) || bEval(e2)
            case bImpl(e1, e2) => bEval(e1) ==> bEval(e2)
            case bIfThenElse(e1, e2, e3) => 
                    if bEval(e1) then bEval(e2) else bEval(e3)

            /*
            And here's the rule for evaluating variable
            expressions. Currently for any variable expression,
            this code just returns true. That is, this code is
            "stubbed out" so that we can at least compile and
            run our codebase. Your job is to provide a correct
            implementation. What this code *should* do is to
            return the value "bound" to the given variable *in
            the provided environment, env*. The environment,
            env, in turn, is just a map that provides a way to
            look up the value of any given variable. Of course
            the map does have to have a value for each variable
            in your expression!
            */
            case bVar(v: variable) => env[v]
        }
    }

    
    /*
    We have defined our own little language, both syntax and semantics
    */
    method Main()
    {
        /*
        We start by constructing three "variables", to which we
        give the convenient names, P, Q, and R. Henceforth we will
        refer to them using these names.
        */
        var P: variable := V(0);
        var Q := V(1);
        var R := V(2);

        /*
        Now you are to build a term representing the Boolean expression
        (P \/ Q) /\ ~R. That is "(P or Q) and (not R)".
        */
        var T := bFalse; // replace bFalse with the correct bExp value

        /*
        Next we construct an environment (a map) that associates a
        Boolean value with each of these variables.
        */
        var env1 := map[P := true, Q := false, R := true];

        /*
        And now finally we can evaluate our Boolean expression, T, in
        the environment, env1, to determine its truth value in the given
        environment. You must understand that to evaluate an expression
        that includes variables, you *must* provide an "environment" that
        "explains" what the value of each parameter is!
        */
        print bEval(T,env1);
    }
}