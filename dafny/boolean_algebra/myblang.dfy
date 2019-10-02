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

    datatype variable = V (n: nat)
    
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
        bVar (v : variable) |

        /*
        And finally we provide constructors for building expressions
        with the usual Boolean connectives.
        */
        bNot(e : bExp) |
        bAnd(e1 : bExp, e2 : bExp) |
        bOr(e1 : bExp, e2 : bExp) |
        bImpl(e1 : bExp, e2 : bExp) |
        bIfThenElse(e1 : bExp, e2 : bExp, e3 : bExp)


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
            case bNot(e') => !bEval(e', env)
            case bAnd(e1, e2) => bEval(e1, env) && bEval(e2, env)
            case bOr(e1, e2) => bEval(e1, env) || bEval(e2, env)
            case bImpl(e1, e2) => bEval(e1, env) ==> bEval(e2, env)
            case bIfThenElse(e1, e2, e3) => 
                    if bEval(e1, env) 
                    then bEval(e2, env) 
                    else bEval(e3, env)

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
            case bVar(v: variable) => lookup(v,env)
        }
    }

    function method lookup(v: variable, env: map<variable, bool>): bool
    {
        if v in env then env[v] else false
    }
    
}