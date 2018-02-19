Set Implicit Arguments.
Unset Strict Implicit.
Require Import Omega List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 50).
Notation "A <<= B" := (forall x, x el A -> x el B) (at level 50).

Inductive form : Type :=
| var : nat -> form
| bot : form
| imp : form -> form -> form.

Notation "s ~> t" := (imp s t) (at level 51, right associativity).
Notation "- s" := (s ~> bot) (at level 35, right associativity).
Reserved Notation "A |- s" (at level 70).

Inductive nd : list form -> form -> Prop :=
| ndA A s : s el A -> A |- s
| ndE A s : A |- bot -> A |- s
| ndII A s t : s::A |- t -> A |- s ~> t
| ndIE A s t : A |- s ~> t -> A |- s -> A |- t
where "A |- s" := (nd A s).

Fact weak A B s :
  A |- s -> A <<= B -> B |- s.
Proof.
  intros H. revert B.
  induction H as [A s H | A s _ IH | A s t _ IH | A s t _ IH1 _ IH2];
    intros B H1.
  - apply ndA. auto.
  - apply ndE. apply IH, H1.
  - apply ndII. apply IH. firstorder.
  - apply ndIE with (s:=s).
    + apply IH1, H1.
    + apply IH2, H1.
Qed.

Fact agree A s t :
  A |- s~>t <-> s::A |- t.
Proof.
  split.
  - intros H % (weak (B:= s::A)).
    + apply (ndIE H). apply ndA; cbn; auto.
    + cbn; auto.
  - apply ndII.
Qed.

Fact cut A s t :
  A |- s -> s::A |- t -> A |- t.
Proof.
  intros H1 H2 % agree. apply (ndIE H2 H1).
Qed.

Fact app2 A s1 s2 t :
  A |- s1 ~> s2 ~> t -> A |- s1 -> A |- s2 -> A |- t.
Proof.
  intros H1 H2 H3.
  apply (ndIE (ndIE H1 H2) H3).
Qed.

Fact DNI A s t :
  s::-t::A |- bot -> A |- --(s~>t).
Proof.
  intros H % agree % agree.
  apply (cut H). clear H.
  apply ndII. apply ndIE with (s:= s~>t).
  { apply ndA; cbn; auto. }
  apply ndII, ndE.
  apply app2 with (s1:= -t) (s2:= s).
  { apply ndA; cbn; auto. }
  - apply ndII.
    apply ndIE with (s:= s~>t).
    { apply ndA; cbn; auto. }
    apply ndII, ndA; cbn; auto.
  - apply ndA; cbn; auto.
Qed.
 
