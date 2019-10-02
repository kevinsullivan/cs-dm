/-
We've already seen that we can assert
that a proposition is true by defining
a variable to have that proposition as
its type, and we can prove the proposition
by assigning a proof term to the variable.
-/

lemma zeqz : 0 = 0 := eq.refl 0

/-
Sometimes it's harder to write an exact
proof term (here, eq.refl 0). In these
cases it can help to figure out a proof
term step by step. Lean supports step
by step development of proof terms with
what are called tactic-based proving.
Here's an equivalent tactic-based proof.
-/

lemma zeqz' : 0 = 0 :=
begin
  apply eq.refl 0,
end

/-
In this case, the proof is so simple
that writing a script is more work.
The key thing to see here, though, is
the "apply" tactic. It applies some
already known rule, here eq.refl, to
move from a state in which something
is to be proved to a state in which
something new has been proved.
-/

/-
Now open the Lean Messages panel by typing
control-shift-enter or command-shift-enter
(Windows/Mac). Now place your cursor first
at the start of the "apply". The message
window will display the "tactic state" at
this point in the script. The state say
that nothing is assumed and the remaining
goal to be proved is 0 = 0. Now move your
cursor to the next line, before the "end."
The tactic state is empty, nothing is left
to be proved, QED. 
-/


/-
EXERCISE. Define zeqz'' as also
being of type 0 = 0, but after the :=,
just write begin on the next line and 
then an end on the following line. You
need to type the begin and end lines
before continuing.
-/


/-
HOW TO SOLVE IT:

Initially there will be an error. Hover
over the red squiggle under the "end."
It tells you that you haven't yet proved
something that remains to be proved, and
it tells you what remains to be proved.
 
Insert a blank line between the begin and 
end. The tactic state tells you what is
known at a given point in a tactic script
(before the turnstile character, ⊢, and 
what remains to be proved, after. Here, 
the goal that remains is 0 = 0. 

If you then click on the next line, end, 
Lean tells you that the proof-generating 
tactic script between the begin and end
lines failed because some goal remains to 
be proved.

In general, a tactic will only partially 
prove a goal, leaving some parts still to 
be proved. In such cases, more tactics 
are then used to finish the construction 
of the required proof. Tactic commands
are separated by commas. We'll see more
later. 

Go ahead and type the required tactic  
between begin and end. Click on the 
line with the tactic, then on the end. Watch how the tactic state changes as 
you go from line to line. 
-/


/-
You might have noticed that while "apply
eq.refl 0" finishes the proof, so does 
just "apply eq.refl". In this case, Lean
infers both arguments to eq.refl from 
context. That, in fact, is what rfl does.
It's not technically a tactic. It is just
using type inference to infer both of the
arguments needed for eq.refl!

Some people refer to such a script as a
proof. A better way to think about it is 
as a step-by-step recipe for building a 
proof. The actual proof at the end of the
day is the proof object that the script
constructs: eq.refl 0, in this case.
-/
