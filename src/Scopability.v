(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines the notions of scoping and scoping preservation. There are more complex and subtle, and should not serve as an introduction to the local reasonning properties.
The main idea is pretty natural: to ensure that newly created objects are hot, we need to check that, transitively, all locations reachable from the attributes of the object are intialized. To do so, we need to be able to reason about the set of locations that are reachable from a set of attributes in a given store. Given two stores [σ] and [σ'], and two sets of locations [L] and [L'], the pair [(σ, L)] "scopes" [(σ',L')] if all locations reachable from [L'] in [σ'] were already reachable from [L] in [σ].
 But as we allow to manipulate objects under initialization, we also need to consider a notion of "preservation" : scoping relations that are maintained when updating from one store to another. *)
From Celsius Require Export PartialMonotonicity Wellformedness Reachability Tactics.
Require Import ssreflect ssrbool Psatz Sets.Ensembles List.
Import ListNotations.
Open Scope nat_scope.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc) (L: LocSet) (el: list Expr).

(** ** Definitions and Notations *)
(* The scoping relation, with the hypothesis that the sets of locations are "correct" (within the stores) *)

Definition scoping σ σ' L L' :=
  L ⪽ σ ->
  L' ⪽ σ' ->
  (forall (l:Loc), l < dom σ -> (σ' ⊨ L' ⇝ l) -> σ ⊨ L ⇝ l).


Notation "( σ1 , L1 )  ⋖  ( σ2 , L2 )" := (scoping σ1 σ2 L1 L2) (at level 0).
Notation "( σ1 ,  { l } )  ⋖  ( σ2 , L2 )" := (scoping σ1 σ2 {l} L2) (at level 0).
Notation "( σ1 , L1 )  ⋖  ( σ2 ,  { l } )" := (scoping σ1 σ2 L1 {l}) (at level 0).
Notation "( σ1 ,  { l1 } )  ⋖  ( σ2 ,  { l2 } )" := (scoping σ1 σ2 {l1} {l2}) (at level 0).

(* The scoping preservation, with technical choices of hypothesis: *)
Definition scoping_preservation σ1 σ2 L :=
  (L ⪽ σ1) /\
  forall σ0 (L0 L1: Ensemble Loc),
    (dom σ0) <= (dom σ1) ->
    (dom σ0) <= (dom σ2) ->
    L0 ⪽ σ0 ->
    L1 ⪽ σ1 ->
    (σ0, L0) ⋖ (σ1, L) ->
    (σ0, L0) ⋖ (σ1, L1) ->
    (σ0, L0) ⋖ (σ2, L1).
Notation "σ1 ⇝ σ2 ⋖ L" := (scoping_preservation σ1 σ2 L) (at level 99).
Local Hint Unfold scoping : scp.
Local Hint Unfold scoping_preservation : scp.
Local Hint Unfold reachability_set: scp.
Local Hint Resolve Union_introl: scp.
Local Hint Resolve Union_intror: scp.
Local Hint Resolve In_singleton: core.

(** ** Basic results *)
(** We first show a set of basic results about scoping. The premisses can sometime look a bit arbitrary, but they are actually fine-tuned *)
Lemma scp_refl :
  forall σ L, (σ, L) ⋖ (σ, L).
Proof.
  eauto with scp.
Qed.
Global Hint Resolve scp_refl: scp.

Lemma scp_refl2 :
  forall σ L1 L2, L2 ⊆ L1 -> (σ, L1) ⋖ (σ, L2).
Proof.
  unfold scoping. steps; rch_set.
  exists l0; steps; eapply H => //.
Qed.
(* Global Hint Resolve scp_refl2: scp. *)

Lemma scp_subset :
  forall σ1 σ2 L L1 L2,
    (σ1, L1) ⋖ (σ2, L2) ->
    L ⊆ L2 ->
    L2 ⪽ σ2  ->
    (σ1, L1) ⋖ (σ2, L).
Proof with (eauto with scp lia).
  unfold scoping; steps ...
  apply H ...
  rch_set.
  exists l0; steps ...
Qed.
(* Global Hint Resolve scp_subset: scp. *)

Lemma scp_union :
  forall σ1 σ2 L L1 L2,
    (σ1, L)  ⋖ (σ2, L1) ->
    (σ1, L)  ⋖ (σ2, L2) ->
    (σ1, L)  ⋖ (σ2, L1∪L2).
Proof with (eauto with wf rch).
  unfold scoping; intros.
  inversion H4; steps...
  inversion H6; steps...
  - apply H5...
    exists x...
  - apply H...
    exists x...
Qed.
Global Hint Resolve scp_union: scp.

Lemma scp_union_introl :
  forall σ1 σ2 L L1 L2,
    (L1 ∪ L2) ⪽ σ2 ->
    (σ1, L) ⋖ (σ2, L1∪L2) ->
    (σ1, L) ⋖ (σ2, L1).
Proof with (eauto with wf rch).
  unfold scoping; intros.
  inversion H4; steps...
  apply H0...
  exists x; split... apply Union_introl...
Qed.
(* Global Hint Resolve scp_union_introl: scp. *)

Lemma scp_union_intror :
  forall σ1 σ2 L L1 L2,
    (L1 ∪ L2) ⪽ σ2 ->
    (σ1, L) ⋖ (σ2, L1∪L2) ->
    (σ1, L) ⋖ (σ2, L2).
Proof with (eauto with wf rch).
  unfold scoping; intros.
  inversion H4; steps...
  apply H0...
  exists x; split... apply Union_intror...
Qed.
(* Global Hint Resolve scp_union_intror: scp. *)

Lemma scp_reachability:
  forall σ l1 l2,
    σ ⊨ l1 ⇝ l2 ->
    (σ, {l1}) ⋖ (σ, {l2}).
Proof with (eauto with rch).
  unfold scoping; intros; rch_set...
Qed.
Global Hint Resolve scp_reachability: scp.

Lemma scp_trans:
  forall σ1 σ2 σ3 L1 L2 L3,
    dom σ1 <= dom σ2 ->
    L2 ⪽ σ2 ->
    (σ1, L1) ⋖ (σ2, L2) ->
    (σ2, L2) ⋖ (σ3, L3) ->
    (σ1, L1) ⋖ (σ3, L3).
Proof with (eauto with scp lia).
  autounfold with notations scp. steps...
Qed.
Global Hint Resolve scp_trans: scp.

Lemma scp_pr_trans:
  forall σ1 σ2 σ3 L1 L2,
    σ1 ⇝ σ2 ⋖ L1 ->
    σ2 ⇝ σ3 ⋖ L2 ->
    (σ1, L1) ⋖ (σ2, L2) ->
    dom σ1 <= dom σ2 ->
    σ1 ⇝ σ3 ⋖ L1.
Proof with (eauto with wf lia).
  unfold scoping_preservation ; light.
  split; [eapply_any |]; steps.
  eapply_any ...
  eapply scp_trans with σ1 L1 ...
Qed.
Global Hint Resolve scp_pr_trans: scp.

Lemma scp_pr_regularity_degenerate:
  forall σ1 σ2 L,
    σ1 ⇝ σ2 ⋖ L ->
    (dom σ1) <= (dom σ2) ->
    (σ1, L) ⋖ (σ2, L).
Proof.
  intros.
  destruct H.
  eapply H1; eauto with lia ss scp.
Qed.
Global Hint Resolve scp_pr_regularity_degenerate: scp.

Lemma scp_pr_regularity:
  forall σ0 σ1 σ2 L L1,
    σ1 ⇝ σ2 ⋖ L ->
    (dom σ0) <= (dom σ2) ->
    (dom σ0) <= (dom σ1) ->
    L ⪽ σ0 ->
    L1 ⪽ σ1 ->
    (σ0, L) ⋖ (σ1, L) ->
    (σ0, L) ⋖ (σ1, L1) ->
    (σ0, L) ⋖ (σ2, L1).
Proof.
  unfold scoping_preservation; steps.
Qed.
(* Global Hint Resolve scp_pr_regularity: scp. *)

Lemma scp_pr_trans_degenerate:
  forall σ1 σ2 σ3 L1 ,
    σ1 ⇝ σ2 ⋖ L1 ->
    dom σ1 <= dom σ2 ->
    σ2 ⇝ σ3 ⋖ L1 ->
    σ1 ⇝ σ3 ⋖ L1.
Proof.
  steps; eauto with scp.
Qed.
Global Hint Resolve scp_pr_trans_degenerate: scp.

Lemma scp_add:
  forall σ σ' ρ' l0 l a,
    (σ, a) ⋖ (σ', {l}) ->
    (σ, a) ⋖ (σ', codom ρ' ∪ {l0}) ->
    (σ, a) ⋖ (σ', codom (l::ρ') ∪ {l0}).
Proof.
  intros.
  assert ((codom (l :: ρ') ∪ {l0}) = Union Loc (Singleton Loc l) ( codom ρ' ∪ {l0})). {
      apply Extensionality_Ensembles.
    unfold Same_set; steps; intros l'; steps;
      inversion H1;
      steps; eauto using Union_introl, Union_intror.
    - inSingleton; subst. apply Union_introl; steps.
    - inversion H2; steps.
      + apply Union_introl; steps.
      + inSingleton; apply Union_intror; steps. }
  rewrite H1; eauto with scp.
Qed.

Lemma scp_add_env:
  forall I v s c e0,
    getObj s I = Some (c, e0) ->
    v < dom s ->
    forall σ0 L0 L2 ,
      L0 ⪽ σ0 ->
      L2 ⪽ s ->
      (σ0, L0) ⋖ (s, {v}) ->
      (σ0, L0) ⋖ (s, L2) ->
      (σ0, L0) ⋖ ([I ↦ (c, e0 ++ [v])] (s), L2).
Proof.
  intros; unfold scoping; simpl; intros.
  destruct H8; steps.
  assert ((s ⊨ x ⇝ l) \/ ((s ⊨ x ⇝ I) /\ (s ⊨ v ⇝ l))) by
      eauto using rch_asgn_new with lia updates.
  steps;
    [ eapply H4 | eapply H3] ;
    simpl; try (eexists; split); eauto with ss.
Qed.
Global Hint Resolve scp_add_env: scp.

Lemma rch_add_empty: forall σ C l1 l2,
    wf σ ->
    (σ ++ [(C, [])]) ⊨ l1 ⇝ l2 ->
    (l1 = dom σ /\ l2 = dom σ) \/ ( σ ⊨ l1 ⇝ l2).
Proof with (updates; eauto with wf rch lia).
  intros.
  remember (σ++[(C,[])]) as σ0.
  induction H0; steps ...
  - assert (l = dom σ \/ l < dom σ) as [|] by lia...
  - eapply getObj_last_empty in H1; steps ...
    right...
Qed.

Lemma rch_add_empty_set: forall σ C L l,
    wf σ ->
    (σ++[(C, [])]) ⊨ L ⇝ l ->
    (σ ⊨ L ⇝ l) \/ l = length σ.
Proof.
  intros.
  inversion H0 as [l1 [Hl1 Hrch]].
  eapply rch_add_empty in Hrch; steps.
  left. exists l1; eauto.
Qed.

(** We prove some specific results on scopability in the context of assignment. The key reasonning technique is to do a case analysis on the presence of the modified entry in the reachability path. *)
Lemma scp_assign:
  forall σ1 σ2 σ2' L1 l l' f C ω,
    σ1 ⇝ σ2 ⋖ L1 ->
    (σ1, L1) ⋖ (σ2, {l}) ->
    (σ1, L1) ⋖ (σ2, {l'}) ->
    getObj σ2 l = Some (C, ω) ->
    σ2' = [l ↦ (C, [f ↦ l']ω)]σ2 ->
    (σ1 ⇝ σ2' ⋖ L1) /\
      ((σ1, L1) ⋖ (σ2', {l})).
Proof with (eauto with scp rch).
  unfold scoping_preservation; intros; flatten.
  repeat split => //.

  - (* σ1 ⇝ σ2' ⋖ L1 *)
    move => σ0 L0 L H_dom1 H_dom2' H_subL H_subL0 A1 A2.
    updates.
    unfold scoping; simpl.
    intros.
    assert ((σ0, L0) ⋖ (σ2, L)) as B1 by eauto.
    assert ((σ0, L0) ⋖ (σ2, {l'})) as C1 by eauto using scp_trans.
    destruct H7 as [l1 [H__l1 H__rch]].
    eapply ss_update in H5.
    lets [? | [H__rch1 H__rch2 ]]: rch_asgn H2 H__rch => //.
    + eapply B1... exists l1...
    + eapply C1... exists l'...

  - (* (σ1, L1) ⋖ (σ2', {l}) *)
    unfold scoping; simpl. intros.
    destruct H7 as [l1 [H__l1 H__rch]].
    ss; updates. inSingleton.
    lets [? | [H__rch1 H__rch2 ]]: rch_asgn H2 H__rch => //.
    + eapply H0... exists l...
    + eapply H1... exists l'...
Qed.

Lemma scp_assign_new:
  forall σ L C,
    wf σ ->
    (σ, L) ⋖ (σ ++ [(C, [])], L).
Proof.
  intros. intros ? ? l ? H__rch.
  apply rch_add_empty_set in H__rch; steps.
  lia.
Qed.
Global Hint Resolve scp_assign_new: scp.
(** ** Evaluation-maintained results *)

(** ** Main Scopability theorem *)
(** We show the main theorem. As for wellformedness theorem, we have to make a custom proof. We use the results shown for initialization, lists and assignment *)
Theorem scp_theorem:
  (forall e σ ρ ψ v σ',
      ⟦e⟧p (σ, ρ, ψ) --> (v, σ') ->
      (codom ρ) ∪ {ψ} ⪽ σ -> wf σ ->
      ((σ, (codom ρ) ∪ {ψ}) ⋖ (σ', {v})) /\ (σ ⇝ σ' ⋖ (codom ρ) ∪ {ψ})) /\
    (forall el σ ρ ψ vl σ',
         ⟦el⟧ (σ, ρ, ψ) --> (vl, σ') ->
         (codom ρ ∪ {ψ}) ⪽ σ ->
         wf σ ->
         ((σ, codom ρ ∪ {ψ}) ⋖ (σ', codom vl)) /\ (σ ⇝ σ' ⋖ (codom ρ ∪ {ψ}))) /\
    (forall C flds I ρ σ σ',
        initP C flds I ρ σ σ' ->
        forall Args Flds Mtds ω,
          (* Hypothesis *)
          wf σ ->
          (codom ρ ∪ {I}) ⪽ σ ->
          ct C = class Args Flds Mtds ->
          getObj σ I = Some (C, ω) ->
          dom ω + dom flds = dom Flds ->
          (* Conclusions *)
          (σ ⇝ σ' ⋖ (codom ρ ∪ {I})) /\
            ((σ, codom ρ ∪ {I}) ⋖ (σ', codom ρ ∪ {I}))).

Proof with (rch_set; updates; eauto 3 with scp wf rch lia).

  apply evalP_multi_ind;
    unfold assign, assign_new in * ; intros; eval_dom; eval_wf.

  - (* e = x *)
    unfold scoping; steps ... ss.
    exists l; split; eauto using getVal_codom with ss.

  - (* this *)
    split; eauto using scp_union_intror with scp.

  - (* e = e0.f *)
    unfold scoping; steps; rch_set; ss.
    assert ((σ,  (codom ρ) ∪ ({ψ})) ⋖ (σ1, {v1})) as C1.
    + eapply scp_trans with σ1 {v1}; eauto with wf.
      unfold scoping; steps.
    + eapply C1 ; steps ...
      eauto with rch.

  - (* e = e0.m(l0) *)
    destruct IH__e0, IH__el; eauto with wf.
    destruct IH__e2; eauto with ss lia.
    assert ((σ, (codom ρ) ∪ {ψ}) ⋖ (σ1, (codom ρ) ∪ {ψ})) as A4 by eauto with scp wf pM.
    assert ((σ, codom ρ ∪ {ψ}) ⋖ (σ2, (codom vl2) ∪ {v1}) ) as A6. {
      eapply scp_union.
      - eauto with scp lia.
      - apply H7...
    }
    split.
    + eapply scp_trans with σ2 ( codom vl2 ∪ {v1}) ...
    + eapply scp_pr_trans with σ2 ( codom vl2 ∪ {v1}) ...

  - (* e = new C(l0) *)
    destruct IH__args; eauto with wf.
    specialize IH__init with Args Flds Mtds [].
    assert (dom σ1 <= dom (σ1 ++ [(C, [])])); updates; try lia.
    destruct IH__init as (? & ?); eauto with wf lia; [| split].
    + ss... eapply ss_trans with σ1...
    + eapply H6; ss; updates; eauto with lia.
      * apply scp_union...
        eapply scp_trans with σ1 (codom vl__args)...
        intros ? ? l ? H__rch. rch_set.
        apply rch_add_empty in H__rch; flatten; try lia; eauto.
        apply rch_dom2 in H__rch1. lia.
      * intros ? ? l ? H__rch.
        rch_set. ss. updates.
        apply rch_add_empty in H__rch; flatten; try lia; eauto.
        apply rch_dom2 in H__rch1; lia.
    + eapply scp_pr_trans; eauto with scp.
      unfold scoping_preservation; steps; eauto.
      apply H6; ss ... apply ss_trans with σ1...
      intros ? ? l ? H__rch. rch_set.
      inverts H__ln...
      * apply rch_add_empty in H__rch; steps. lia.
        apply H12...
        exists l0...
      * apply rch_add_empty in H__rch; steps; try lia.
        apply rch_dom2 in H17...

  - (* e = e0.f = e1; e2 *)
    destruct (getObj σ2 v1) as [[C ω] |] eqn: H__obj.
    + destruct IH__e1; eauto.
      destruct IH__e2; eauto with wf lia.
      destruct IH__e'; eauto with wf lia.
      eapply scp_assign with (f := x) (σ1 := σ) (l' := v2) (L1 := (codom ρ ∪ {ψ})) in H__obj as [ ];
        try reflexivity; eauto 3 with wf lia scp; [split |].
      * eapply scp_trans with (σ2 := [v1 ↦ (C, [x ↦ v2] (ω))]σ2) (L2 := codom ρ ∪ {ψ});
          try eapply H8; eauto 3 with wf lia scp updates.
      * eapply scp_pr_trans_degenerate with (σ2 := [v1 ↦ (C, [x ↦ v2] (ω))] (σ2)) ; eauto with scp lia...
      * eapply_any ...
    + destruct IH__e1; eauto.
      destruct IH__e2; eauto with wf lia.
      destruct IH__e'; eauto with wf lia.
      split.
      * eapply scp_trans with (σ2 := σ2) (L2 := codom ρ ∪ {ψ}) ...
      * eapply scp_pr_trans ...

  - (* el_nil *)
    split.
    + intros x; steps.
      inversion H3; steps.
    + eapply scp_pr_trans_degenerate ...

  - (* el_cons *)
    destruct IH__e; eauto.
    destruct IH__el; eauto with wf lia.
    split.
    + rewrite codom_cons.
      eapply scp_union.
      * apply_any; eauto with lia wf scp.
      * eapply scp_trans with (σ2 := σ1) (L2 := codom ρ ∪ {ψ}) ...
    + eapply scp_pr_trans_degenerate ...

  - (* init_nil *)
    steps ...

  - (* init_cons *)
    destruct IH__e; eauto.
    lets [?ω [ ]]: eM_theorem_expr H__e H2; cross_rewrites.
    rewrite H8 in H__assign. inverts H__assign.
    specialize (IH__flds Args Flds Mtds (ω0++[v])).
    simpl in *.
    destruct IH__flds as (? & ?); updates; eauto with updates wf lia; split.
    + unfold scoping_preservation; steps. apply H10...
      * eapply scp_add_env; eauto with lia wf; updates;
        eapply scp_trans with σ (codom ρ ∪ {I})...
      * eapply scp_add_env; eauto with lia wf; updates.
        eapply scp_trans with σ (codom ρ ∪ {I})...
        apply H7...
    + apply H10 ...
Qed.

Corollary scp_theorem_expr:
  forall e σ ρ ψ v σ',
    ⟦e⟧p (σ, ρ, ψ) --> (v, σ') ->
    (codom ρ) ∪ {ψ} ⪽ σ -> wf σ ->
    ((σ, (codom ρ) ∪ {ψ}) ⋖ (σ', {v})) /\ (σ ⇝ σ' ⋖ (codom ρ) ∪ {ψ}).
Proof.
  apply scp_theorem.
Qed.

Corollary scp_theorem_init:
  forall C flds I ρ σ σ',
        initP C flds I ρ σ σ' ->
        forall Args Flds Mtds ω,
          (* Hypothesis *)
          wf σ ->
          (codom ρ ∪ {I}) ⪽ σ ->
          ct C = class Args Flds Mtds ->
          getObj σ I = Some (C, ω) ->
          dom ω + dom flds = dom Flds ->
          (* Conclusions *)
          (σ ⇝ σ' ⋖ (codom ρ ∪ {I})) /\
            ((σ, codom ρ ∪ {I}) ⋖ (σ', codom ρ ∪ {I})).
Proof.
  apply scp_theorem.
Qed.
