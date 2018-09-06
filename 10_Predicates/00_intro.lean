-- UNDER CONSTRUCTION

/-
Every Person is Mortal, Socrates is a Person
---------------------------------------------
             Socrates is Mortal


Incorporating the notio of proof, and moving
to more mathematical notation, we could write
this as follows:

prog : (∀ p : Person), Mortal p; p: Person
------------------------------------------
        pf : (Mortal p)

From a proof, mort, of Person → Mortal "If p 
is a Person then p is Mortal" and from (a proof 
of) "Socrates is a person" we derive (a proof 
of) "Socrates is Mortal." 

We can write "if p is any person then p is
mortal" as Person → Mortal. 

    ∀ p : Person, (mortal P)

Another way to say that all people are 
mortal is to say that every person is
-/