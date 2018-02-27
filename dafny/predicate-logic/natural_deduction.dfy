include "consequence.dfy"

module natural_deduction
{
    import opened syntax
    import opened consequence

    /*
    datatype nd_proves  = 
        exfalso_quodlibet(cx: context, p: prop)
    */

    // allow proposition to be in context more than once
    class proofState
    {
        var goal: prop;
        var contxt: map<string, prop>;

        constructor proofState(g: prop)
          ensures contxt == map[] && goal == g;
        {
          contxt := map[];
          goal := g;
        }

        /*
        Warning! Assuming goal as axiom gets no credit.
        Assuming False, or equivalent, gets no credit.
        */

        method axiom(p: prop, lbl: string) returns (error: bool)
            requires lbl !in contxt;
        {
            contxt := contxt[lbl := p];
        }

        method andIntro(l1: string, l2: string, lbl: string) returns (error: bool)
          requires l1 in contxt && l2 in contxt;
        {
          contxt := contxt[lbl := pAnd(contxt(l1),contxt(l2))];
        }
    }

    method ex_falso(sq: sequent) returns (rsq: sequent, b: bool)
    {
        var cntx := sq.0;
        var conc := sq.1;
        if proved(cntx, pFalse) {}
    }

    method proved(cx: context, p:prop) returns (r: bool) {return true;} // stub}
}

/*
Inductive classic_ND_proves : list (prop atom) -> prop atom -> Prop :=
| classic_ND_exfalso_quodlibet {Γ P} :
  Γ ⊢c ⊥ ->
  Γ ⊢c P
| classic_ND_True_intro {Γ} :
  Γ ⊢c ⊤
| classic_ND_or_introl {Γ P Q} :
  Γ ⊢c P ->
  Γ ⊢c P ∨ Q
| classic_ND_or_intror {Γ P Q} :
  Γ ⊢c Q ->
  Γ ⊢c P ∨ Q
| classic_ND_proof_by_cases {Γ P Q R} :
  Γ ⊢c P ∨ Q ->
  P :: Γ ⊢c R ->
  Q :: Γ ⊢c R ->
  Γ ⊢c R
| classic_ND_and_intro {Γ P Q} :
  Γ ⊢c P ->
  Γ ⊢c Q ->
  Γ ⊢c P ∧ Q
| classic_ND_and_elim {Γ P Q R} :
  Γ ⊢c P ∧ Q ->
  P :: Q :: Γ ⊢c R ->
  Γ ⊢c R
| classic_ND_cond_proof {Γ P Q} :
  P :: Γ ⊢c Q ->
  Γ ⊢c P ⊃ Q
| classic_ND_modus_ponens {Γ P Q} :
  Γ ⊢c P ⊃ Q ->
  Γ ⊢c P ->
  Γ ⊢c Q
| classic_ND_assumption {Γ P} :
  In P Γ ->
  Γ ⊢c P
| classic_ND_cut {Γ P Q} :
  Γ ⊢c P ->
  P :: Γ ⊢c Q ->
  Γ ⊢c Q
| classic_ND_proof_by_contradiction {Γ P} :
  ¬P :: Γ ⊢c ⊥ ->
  Γ ⊢c P
where "Γ ⊢c P" := (classic_ND_proves Γ P).
*/