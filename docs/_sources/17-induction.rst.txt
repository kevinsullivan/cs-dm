*******************
Proofs of Existence
*******************

Predicate logic allows for existentially quantified propositions. For
a simple example, one might claim that there exists a natural number,
$n$, such that $n = 3 + 1$. That is :math:`\exists n, n = 3 + 1`. In
the constructive logic of Lean, and in type theory more generally, a
proof of such a proposition is a basically pair. The first element of
such a pair is a value that satisfies the given condition. We call a
value of this kind a *witness*. The second element of the pair is a
*proof* that that particular value satisifies the condition.

There is a witness in this case. It's the number, *4*. And there is a
proof that $4 = 3 + 1$, namely $rfl$. The proof of the proposition,
:math:`\exists n, n = 3 + 1` is thus, in essence, the ordered pair,
$(4, rfl)$. In this chapter we explain these ideas in more detail and
show how to construct such proofs in Lean. We end with a discussion of
differences in existence proofs in constructive and classical logic.

More to come.
