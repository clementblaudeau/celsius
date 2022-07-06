(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL & Inria 2020-2022 *)
(* ------------------------------------------------------------------------ *)
(* This file defines the notion of wellformedness for scopes. The set of reachable locations must
all be valid locations of the store - that is, locations that are inside of the store. The main
result is to show that if we start from a wellformed store that contains the local environment ρ and
the [this] pointer, then we end up with a wellformed store that contains the location of the
result *)

From Celsius Require Export PartialMonotonicity Reachability.
Require Import ssreflect ssrbool Psatz List Sets.Ensembles Coq.Program.Tactics Coq.Sets.Finite_sets_facts.
Import ListNotations.
Open Scope nat_scope.

(** ** Implicit types *)
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc) (flds: list Field) (el: list Expr).

(** ** Definitions and notations *)
(** A wellformed store only contains pointers to locations that are within itself *)
Definition wf σ :=
  forall l C ω,
    getObj σ l = Some(C, ω) ->
    (forall Args Flds Mtds,
        ct C = class Args Flds Mtds ->
        dom ω <= dom Flds) /\
      (forall f l',
          getVal ω f = Some l' ->
          l' < dom σ).

Lemma wf_proj1 : forall σ l C ω f v,
    wf σ ->
    getObj σ l = Some (C, ω) ->
    getVal ω f = Some v ->
    v < dom σ.
Proof.
  intros.
  eapply H; eauto.
Qed.
Global Hint Resolve wf_proj1: wf.

Lemma wf_proj2 : forall σ l C ω Args Flds Mtds,
    wf σ ->
    getObj σ l = Some (C, ω) ->
    ct C = class Args Flds Mtds ->
    dom ω <= dom Flds.
Proof.
  intros.
  eapply H; eauto.
Qed.
Global Hint Resolve wf_proj2: wf.


(** In preparation for initialization theorems, we have technical results about adding a location *)
Lemma wf_add : forall s C ρ Args Flds Mtds,
    wf s ->
    codom ρ ⪽ s ->
    ct C = class Args Flds Mtds ->
    dom ρ <= dom Flds ->
    wf (s ++ [(C,ρ)]).
Proof with (eauto with wf lia).
  steps.
  unfold wf; simpl; intros.
  rewrite app_length; simpl.
  destruct_eq (l = length s);
    [subst; try rewrite_anywhere getObj_last | try rewrite_anywhere getObj_last2].
  + steps.
    specialize (H0 l') as [ ] ...
    eapply getVal_codom...
  + split; intros...
    lets [ _ ? ]: H H3 ...
    lets : H5 H4 ...
  + apply getObj_dom in H3.
    rewrite_anywhere  app_length; simpl in *.
    assert (l < length s) by lia ; eauto.
Qed.
Global Hint Resolve wf_add: wf.

Lemma wf_add_empty : forall s C,
    wf s ->
    wf (s ++ [(C,[])]).
Proof.
  intros.
  destruct (ct C) eqn:H__ct.
  eapply wf_add; eauto using ss_codom_empty with cbn lia.
Qed.
Global Hint Resolve wf_add_empty: wf.


(** ** Evaluation-maintained results *)
(** First a technical result on assignment *)
Lemma wf_assign:
  forall σ ω l v f C,
    (getObj σ l) = Some (C, ω) ->
    v < dom σ ->
    wf σ ->
    wf [l ↦ (C, [f ↦ v]ω)]σ .
Proof.
  unfold wf; intros; updates.
  lets [ ]: H1 H.
  destruct_eq (l = l0); subst; updates.
  - split; intros; eauto.
    destruct_eq (f = f0); subst; updates; eauto.
  - lets [ ]: H1 H2.
    split; intros; eauto.
Qed.
Global Hint Resolve wf_assign: wf.

Lemma wf_assign_new:
  forall C σ σ' I x v ω Args Flds Mtds,
    ct C = class Args Flds Mtds ->
    wf σ ->
    v < dom σ ->
    x < length Flds ->
    getObj σ I = Some (C, ω) ->
    assign_new I x v σ = Some σ' ->
    wf σ'.
Proof with (updates; cross_rewrites; eauto with wf lia).
  unfold assign_new; intros.
  steps.
  rewrite_anywhere PeanoNat.Nat.eqb_eq... steps.
  unfold wf; intros; updates.
  destruct_eq (I = l); subst; split; intros; cross_rewrites; updates...
  eapply getVal_add in H4; steps...
  eapply H0...
Qed.


(** Then we have the main result *)
Theorem wf_theorem :
  (forall e σ ρ ψ v σ',
      ⟦e⟧ (σ, ρ, ψ) --> (v, σ') ->
      wf σ ->
      (codom ρ) ∪ {ψ} ⪽ σ ->
      (wf σ' /\ v < dom σ')) /\
    (forall el σ ρ ψ vl σ',
        ⟦ el ⟧ (σ, ρ, ψ) --> (vl, σ') ->
        (codom ρ ∪ {ψ}) ⪽ σ ->
        wf σ ->
        wf σ' /\ (codom vl ⪽ σ')) /\
    (forall C ψ x ρ σ σ',
        initP C ψ x ρ σ σ' ->
        forall ω,
          getObj σ ψ = Some (C, ω) ->
          let '(class _ Flds _ ) := ct C in
          x <= length Flds ->
          codom ρ ∪ {ψ} ⪽ σ ->
          wf σ -> wf σ').
Proof with (updates; cross_rewrites; eauto 4 with wf ss lia).

  eapply evalP_multi_ind;
    unfold assign; simpl; intros;
    eval_dom; ss_trans...

  - (* e_var *)
    split...

  -  (* e_fld *)
    destruct IH__e0...

  - (* e_mtd *)
    destruct IH__e0 ...
    destruct IH__el ...

  - (* e_new *)
    destruct IH__args ...
    split... rewrite H__ct in IH__init.
    destruct Flds; [steps; inverts H__init|]...
    + inverts H6.
    + eapply IH__init; ss;
      try eapply ss_trans with σ1; simpl...

  - (* e_assgn *)
    destruct IH__e1 ...
    destruct IH__e2 ...
    repeat destruct_match; subst;
      destruct IH__e'...
    + apply ss_trans with σ...
    + lets [ ]: getObj_Some σ2 v1; steps...

  - (* el_cons *)
    destruct IH__e ...
    destruct IH__el ...
    split... rewrite codom_cons...

  - (* init_nil *)
    steps.

  - (* init_cons *)
    rewrite H__ct.
    intros.
    destruct IH__e ...
    lets: pM_theorem_expr H__e.
    lets: pM_assign_new H__assign.
    lets (?C & ?ω & ?): getObj_Some σ I...
    lets (?ω & ? & ?): H7 I...
    lets (?ω & ? & ?): H8 I...
    lets: init_field H__init...
    lets: wf_assign_new C0 H__assign...
    rewrite H__ct in IH__init.
    eapply IH__init; eauto;
      try eapply ss_trans with σ...
    eauto with pM lia.
Qed.

Corollary wf_theorem_expr :
  forall e σ ρ ψ v σ',
    ⟦e⟧ (σ, ρ, ψ) --> (v, σ') ->
    wf σ ->
    (codom ρ) ∪ {ψ} ⪽ σ ->
    (wf σ' /\ v < dom σ').
Proof.
  apply wf_theorem.
Qed.

Corollary wf_theorem_list :
  forall el σ ρ ψ vl σ',
    ⟦ el ⟧ (σ, ρ, ψ) --> (vl, σ') ->
    (codom ρ ∪ {ψ}) ⪽ σ ->
    wf σ ->
    wf σ' /\ (codom vl ⪽ σ').
Proof.
  apply wf_theorem.
Qed.

Corollary wf_theorem_init :
  forall C ψ x ρ σ σ',
    initP C ψ x ρ σ σ' ->
    forall ω,
      getObj σ ψ = Some (C, ω) ->
      let '(class _ Flds _ ) := ct C in
      x <= length Flds ->
      codom ρ ∪ {ψ} ⪽ σ ->
      wf σ -> wf σ'.
Proof.
  intros.
  lets (_ & _ & ?): wf_theorem.
  specialize (H1 C).
  ct_lookup C.
  eapply H1; eauto.
Qed.

(* A simple corollary on the conservation of wellformedness *)
Corollary wf_conserved :
  forall e σ ρ ψ v σ',
    ⟦e⟧p(σ, ρ, ψ) --> (v, σ') ->
    wf σ ->
    (codom ρ) ∪ {ψ} ⪽ σ ->
    wf σ'.
Proof.
  eapply wf_theorem.
Qed.
Global Hint Resolve wf_conserved: wf.

(** Another consequence: the returned value is within the returned store: *)
Corollary correct_value :
  forall e σ ρ ψ v σ',
    ⟦e⟧p (σ, ρ, ψ) --> (v, σ') ->
    wf σ ->
    (codom ρ) ∪ {ψ} ⪽ σ ->
    v < dom σ'.
Proof.
  eapply wf_theorem.
Qed.
Global Hint Resolve correct_value: wf.

(** A useful tactic: *)
Ltac eval_wf :=
  repeat
    match goal with
    | H: codom ?ρ ∪ {?ψ} ⪽ ?σ1, H2: dom ?σ1 <= dom ?σ2 |- _ =>
        let name := fresh "H__codom" in
        add_hypothesis name (ss_trans _ σ1 σ2 H2 H)
    | H:⟦ ?e ⟧p (?σ, ?ρ, ?ψ) --> (?v, ?σ'),
        H1:wf ?σ,
          H2 : codom ?ρ ∪ {?ψ} ⪽ ?σ
      |- _ =>
        match goal with
        | H':wf σ' |- _ => fail 1
        | _ =>
            let H_val := fresh "H_val" in
            let H_wf := fresh "H_wf" in
            pose proof (wf_theorem_expr e σ ρ ψ v σ' H H1 H2) as [H_wf H_val]
        end
    | H:⟦_ ?el _⟧p (?σ, ?ρ, ?ψ) --> (?vl, ?σ'),
        H1:wf ?σ,
          H2 : codom ?ρ ∪ {?ψ} ⪽ ?σ
      |- _ =>
        match goal with
        | H':wf σ' |- _ => fail 1
        | _ =>
            let H_val := fresh "H_val" in
            let H_wf := fresh "H_wf" in
            pose proof (wf_theorem_list el σ ρ ψ vl σ' H H2 H1) as [H_wf H_vals]
        end
    end.

(** Partially monotonic wellformed stores keep objects warm *)
Lemma pM_wf_warm_monotone:
  forall σ σ' l,
    σ ⪯ σ' ->
    wf σ' ->
    σ  ⊨ l : warm ->
    σ' ⊨ l : warm.
Proof.
  intros.
  inverts H1.
  lets (?ω & ? & ?): H l H2.
  lets [? _]: H0 l H1.
  eapply sm_warm; eauto with rch lia.
Qed.
