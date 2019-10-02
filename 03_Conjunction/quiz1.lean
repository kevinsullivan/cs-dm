/-
Prove that from a proof of
(P ∧ Q) ∧ R you can derive a
proof of P ∧ (Q ∧ R). Note 
that ∧ is right-associative.
This means that P ∧ Q ∧ R is
defined to mean P ∧ (Q ∧ R).

Note: we changed the name of
the premise/argument. It was 
pfP_QR. A better name, which
we use here, is pfPQ_R.

To do this quiz, replace the
"sorry" with you answer. It
can be either in the form 
of an exact proof term or in
the form of a tactic script.  
-/

def and_assoc_r 
  { P Q R : Prop } 
  (pfPQ_R: (P ∧ Q) ∧ R) : 
    (P ∧ (Q ∧ R)) := 
      sorry

  