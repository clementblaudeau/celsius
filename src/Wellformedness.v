(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines the notion of wellformedness for scopes. The set of reachable locations must all be valid locations of the store - that is, locations that are inside of the store. The main result is to show that if we start from a wellformed store that contains the local environment ρ and the [this] pointer, then we end up with a wellformed store that contains the location of the result *)

From Celsius Require Export Reachability Semantics PartialMonotonicity.
Require Import ssreflect ssrbool Psatz List Sets.Ensembles Coq.Program.Tactics Coq.Sets.Finite_sets_facts.
Import ListNotations.
Open Scope nat_scope.

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
  eapply wf_add; eauto using storeSubset_codom_empty with cbn lia.
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
  unfold wf; intros.
  rewrite update_dom.
  getObj_update.
  destruct H2; steps;
    try rewrite update_one3; steps;
    try solve [eapply H1; eauto].
  getVal_update; steps; eauto.
  eapply H1; eauto.
Qed.
Global Hint Resolve wf_assign: wf.
Global Hint Unfold storeSubset: wf.

Ltac cross_rewrites :=
  repeat match goal with
         | H: ?A = ?B, H': ?A = ?C |- _ => rewrite H in H'; inverts H'
         end.


(** Then we have the main result *)
Theorem wf_theorem :
 forall e σ ρ ψ v σ',
    ⟦e⟧ (σ, ρ, ψ) --> (v, σ') ->
    wf σ ->
    (codom ρ) ∪ {ψ} ⪽ σ ->
    (wf σ' /\ v < dom σ').
Proof with (update_dom; eauto with wf pM updates lia).
  intros.
  move: H0 H1.
  induction H using evalP_ind2 with
    (Pl := fun _ σ ρ ψ vl σ' _ => (codom ρ ∪ {ψ}) ⪽ σ -> wf σ -> (wf σ' /\ codom vl ⪽ σ'))
    (Pin := fun C flds ψ ρ σ σ' _ =>
              forall (H__codom : codom ρ ∪ {ψ} ⪽ σ) (H__wf: wf σ) ω Args Flds Mtds
                (H__ct : ct C = class Args Flds Mtds) (H__obj: getObj σ ψ = Some(C, ω)),
                dom ω + dom flds = dom Flds ->
                 (exists ω', getObj σ' ψ = Some (C, ω') /\ dom ω' = dom Flds) /\ wf σ');
    unfold assign, assign_new in * ; intros; eval_dom ...
  - (* e_var *)
    intuition auto ...
  - (* e_fld *)
    destruct IHevalP1...
    destruct IHevalP2...
  - (* e_new *)
    destruct IHevalP ...
    edestruct IHevalP0; eauto with lia wf.
    + eapply storeSubset_union;
      [ eapply storeSubset_trans with σ1 |
        eapply storeSubset_singleton3] ; try rewrite dom_app ...
    + rewrite getObj_last ...
    + reflexivity.
  - (* e_assgn *)
    destruct IHevalP1 ...
    destruct IHevalP2 ...
    repeat destruct_match; subst;
      destruct IHevalP3 ...
  - (* el_cons *)
    destruct IHevalP ...
    destruct IHevalP0; steps ...
    apply storeSubset_add...
  - (* init_nil *)
    simpl in *.
    split; [eexists; split |] ...
  - (* init_cons *)
    destruct IHevalP ...
    destruct (getObj σ1 I) as [[?C ?ω] |] eqn:?H__obj;
      repeat rewrite_anywhere update_dom ...
    invert_constructor_equalities; subst. update_dom.
    simpl in H0.
    lets [?ω [ ] ]: eM_theorem H H__obj. cross_rewrites.
    edestruct IHevalP0; eauto.
    + eapply storeSubset_trans with σ ...
    + intros l ?C ?ω ?H__obj; update_dom.
      destruct_eq (l = I); subst.
      * rewrite getObj_update1 in H__obj1. apply getObj_dom in H__obj ...
        invert_constructor_equalities; subst.
        pose proof H__obj0.
        split.
        -- intros; cross_rewrites. rewrite app_length; simpl ...
        -- intros.
           apply getVal_add in H7; steps ...
           eapply wf_proj1 ...
      * rewrite getObj_update2 in H__obj1; eauto. apply getObj_dom in H__obj ...
    + rewrite getObj_update1 ...
    + rewrite app_length; simpl ...
Qed.

Corollary wf_theorem_list :
  forall (el: list Expr) σ ρ ψ vl σ',
    ⟦ el ⟧ (σ, ρ, ψ) --> (vl, σ') ->
    (codom ρ ∪ {ψ}) ⪽ σ ->
    wf σ ->
    wf σ' /\ (codom vl ⪽ σ').
Proof with (eauto with wf lia).
  intros. move: H0 H1.
  induction H; steps;
    eval_dom ...
  + eapply wf_theorem in H; steps .
    apply IHevalListP ...
  + eapply wf_theorem in H; steps.
    eapply storeSubset_add; steps ...
    apply IHevalListP ...
Qed.
Global Hint Resolve wf_theorem_list: wf.

Corollary wf_theorem_init :
  forall C flds ψ ρ σ σ' Args Flds Mtds ω,
    initP C flds ψ ρ σ σ' ->
    codom ρ ∪ {ψ} ⪽ σ ->
    wf σ ->
    ct C = class Args Flds Mtds ->
    getObj σ ψ = Some(C, ω) ->
    dom ω + dom flds = dom Flds ->
    (exists ω', getObj σ' ψ = Some (C, ω') /\ dom ω' = dom Flds) /\ wf σ'.
Proof with (update_dom; eauto with wf lia).
  intros. move: H0 H1 H2 H3 H4. gen ω.
  induction H; intros; eval_dom ...
  - steps ...
  - simpl in *.
    lets [ ] : wf_theorem H; eauto.
    unfold assign_new in *.
    destruct (getObj σ1 I) as [[?C ?ω] |] eqn:?H__obj; update_dom ...
    invert_constructor_equalities; subst ...
    lets [?ω [ ] ]: eM_theorem H H5. cross_rewrites.
    eapply IHinitP ...
    + eapply storeSubset_trans with σ ...
    + intros l ?C ?ω ?H__obj; update_dom.
      destruct_eq (l = I); subst.
      * rewrite getObj_update1 in H__obj0. apply getObj_dom in H5 ...
        invert_constructor_equalities; subst.
        pose proof H__obj.
        split.
        -- intros; cross_rewrites. rewrite app_length; simpl ...
        -- intros.
           apply getVal_add in H12; steps ...
           eapply wf_proj1 ...
      * rewrite getObj_update2 in H__obj0; eauto. apply getObj_dom in H__obj ...
    + rewrite getObj_update1 ...
    + rewrite app_length; simpl ...
Qed.
Global Hint Resolve wf_theorem_list: wf.


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
        add_hypothesis name (storeSubset_trans _ σ1 σ2 H2 H)
    | H:⟦ ?e ⟧p (?σ, ?ρ, ?ψ) --> (?v, ?σ'),
        H1:wf ?σ,
          H2 : codom ?ρ ∪ {?ψ} ⪽ ?σ
      |- _ =>
        match goal with
        | H':wf σ' |- _ => fail 1
        | _ =>
            let H_val := fresh "H_val" in
            let H_wf := fresh "H_wf" in
            pose proof (wf_theorem e σ ρ ψ v σ' H H1 H2) as [H_wf H_val]
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
  forall σ σ' (l: Loc),
    σ ⪯ σ' ->
    wf σ' ->
    σ  ⊨ l : warm ->
    σ' ⊨ l : warm.
Proof.
  autounfold with pM core notations. unfold reachable_warm.
  steps.
  lets [?ω' [ ] ] : H H2.
  lets [ ? _ ]: H0 H3.
  lets : H6 H1.
  repeat eexists; eauto with lia.
Qed.
