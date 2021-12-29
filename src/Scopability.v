(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines the notions of scoping and scoping preservation. There are more complex and subtle, and should not serve as an introduction to the local reasonning properties.
The main idea is pretty natural: to ensure that newly created objects are hot, we need to check that, transitively, all locations reachable from the attributes of the object are intialized. To do so, we need to be able to reason about the set of locations that are reachable from a set of attributes in a given store. Given two stores [σ] and [σ'], and two sets of locations [L] and [L'], the pair [(σ, L)] "scopes" [(σ',L')] if all locations reachable from [L'] in [σ'] were already reachable from [L] in [σ].
 But as we allow to manipulate objects under initialization, we also need to consider a notion of "preservation" : scoping relations that are maintained when updating from one store to another. *)

From Celsius Require Export PartialMonotonicity Compatibility Wellformedness Reachability Tactics.
Require Import ssreflect ssrbool Psatz Sets.Ensembles List.
Import ListNotations.
Open Scope nat_scope.

(** ** Definitions and Notations *)
(* The scoping relation, with the hypothesis that the sets of locations are "correct" (within the stores) *)
Definition scoping (σ σ': Store) (L L': Ensemble Loc) :=
  L ⪽ σ ->
  L' ⪽ σ' ->
  (forall l, l < dom σ -> (σ' ⊫ L' ⇝ l) -> σ ⊫ L ⇝ l).

Notation "( σ1 , L1 )  ⋖  ( σ2 , L2 )" := (scoping σ1 σ2 L1 L2) (at level 0).
Notation "( σ1 , { l } )  ⋖  ( σ2 , L2 )" := (scoping σ1 σ2 {l} L2) (at level 0).
Notation "( σ1 , L1 )  ⋖  ( σ2 , { l } )" := (scoping σ1 σ2 L1 {l}) (at level 0).
Notation "( σ1 , { l1 } )  ⋖  ( σ2 , { l2 } )" := (scoping σ1 σ2 {l1} {l2}) (at level 0).


(* The scoping preservation, with technical choices of hypothesis: *)
Definition scoping_preservation (σ1 σ2: Store) (L: LocSet) :=
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

Global Hint Unfold scoping : scp.
Global Hint Unfold scoping_preservation : scp.
Global Hint Unfold reachability_set: scp.
Global Hint Resolve Union_introl: scp.
Global Hint Resolve Union_intror: scp.


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
  unfold scoping, reachability_set; steps.
  exists l'; steps; eapply H => //.
Qed.
Global Hint Resolve scp_refl2: scp.

Lemma scp_subset :
  forall σ1 σ2 L L1 L2,
    (σ1, L1) ⋖ (σ2, L2) ->
    L ⊆ L2 ->
    L2 ⪽ σ2  ->
    (σ1, L1) ⋖ (σ2, L).
Proof with (eauto with scp).
  unfold scoping, reachability_set; steps ...
Qed.
Global Hint Resolve scp_subset: scp.

Lemma scp_union :
  forall σ1 σ2 L L1 L2,
    (σ1, L)  ⋖ (σ2, L1) ->
    (σ1, L)  ⋖ (σ2, L2) ->
    (σ1, L)  ⋖ (σ2, L1∪L2).
Proof.
  unfold scoping, reachability_set; steps.
  inversion H4; steps; eauto with wf.
Qed.
Global Hint Resolve scp_union: scp.

Lemma scp_union_introl :
  forall σ1 σ2 L L1 L2,
    (L1 ∪ L2) ⪽ σ2 ->
    (σ1, L) ⋖ (σ2, L1∪L2) ->
    (σ1, L) ⋖ (σ2, L1).
Proof.
  unfold scoping, reachability_set; steps.
  eauto with scp.
Qed.
Global Hint Resolve scp_union_introl: scp.

Lemma scp_union_intror :
  forall σ1 σ2 L L1 L2,
    (L1 ∪ L2) ⪽ σ2 ->
    (σ1, L)  ⋖ (σ2, L1∪L2) ->
    (σ1, L)  ⋖ (σ2, L2).
Proof.
  unfold scoping, reachability_set; steps.
  eauto with scp.
Qed.
Global Hint Resolve scp_union_intror: scp.


Lemma scp_reachability:
  forall σ l1 l2,
    σ ⊨ l1 ⇝ l2 ->
    (σ, {l1}) ⋖ (σ, {l2}).
Proof.
  unfold scoping, reachability_set ; steps.
  eauto with scp.
  exists l1; try inSingleton; steps; eauto with scp rch.
Qed.
Global Hint Resolve scp_reachability: scp.


Lemma scp_trans:
  forall σ1 σ2 σ3 L1 L2 L3,
    dom σ1 <= dom σ2 ->
    L2 ⪽ σ2 ->
    (σ1, L1) ⋖ (σ2, L2) ->
    (σ2, L2) ⋖ (σ3, L3) ->
    (σ1, L1) ⋖ (σ3, L3).
Proof with eauto with scp lia.
  unfold scoping, reachability_set; steps...
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
  unfold scoping_preservation, scoping; simpl; steps.
  eauto with scp.
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
Global Hint Resolve scp_pr_regularity: scp.

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
      eauto using reachability_add_env with updates.
  steps;
    [ eapply H4 | eapply H3] ;
    simpl; try (eexists; split); eauto with wf.
Qed.
Global Hint Resolve scp_add_env: scp.

Lemma reachability_not_empty: forall σ C l1 l2,
    wf σ ->
    (σ++[(C, [])]) ⊨ l1 ⇝ l2 ->
    (l1 = dom σ /\ l2 = dom σ) \/ ( σ ⊨ l1 ⇝ l2).
Proof with (eauto with rch).
  intros.
  remember (σ++[(C,[])]) as σ0.
  induction H0; steps ...
  - rewrite dom_app in H0; steps.
    apply le_S_n in H0.
    destruct (Lt.le_lt_or_eq _ _ H0); steps.
    right. steps ...
  - eapply getObj_last_empty in H1; steps ...
Qed.

Lemma reachability_add_empty: forall σ C L l,
    wf σ ->
    (σ++[(C, [])]) ⊫ L ⇝ l ->
    (σ ⊫ L ⇝ l) \/ l = length σ.
Proof.
  intros.
  inversion H0 as [l1 [Hl1 Hrch]].
  eapply reachability_not_empty in Hrch; steps.
  left. exists l1; eauto.
Qed.

(** ** Assignment results *)
(** We prove some specific results on scopability in the context of assignment. The key reasonning technique is to do a case analysis on the presence of the modified entry in the reachability path. *)

Lemma scp_assign:
  forall σ1 σ2 σ2' L1 l l' f C ω ω',
    σ1 ⇝ σ2 ⋖ L1 ->
    (σ1, L1) ⋖ (σ2, {l}) ->
    (σ1, L1) ⋖ (σ2, {l'}) ->
    getObj σ2 l = Some (C, ω) ->
    ω' = [f ↦ l']ω ->
    σ2' = [l ↦ (C, ω')]σ2 ->
    (σ1 ⇝ σ2' ⋖ L1) /\ ((σ1, L1) ⋖ (σ2', {l})).
Proof.
  unfold scoping_preservation; light; flatten.
  split.
  - (* σ1 ⇝ σ2' ⋖ L1 *)
    split; eauto.
    move => σ0 L0 L H_dom1 H_dom2' H_subL H_subL0 A1 A2.
    intros. update_dom.
    unfold scoping; simpl.
    intros.
    assert ((σ0, L0) ⋖ (σ2, L)) as B1 by eauto.
    assert ((σ0, L0) ⋖ (σ2, {l'})) as C1 by eauto using scp_trans.
    destruct H7; steps.
    eapply storeSubset_update in H5.
    destruct_eq (l = l'); subst.
    + (* l = l' , the assignment is weakening *)
      eapply B1; simpl; (try exists x); eauto using reachability_weaken_assignment with wf.
    + (* l ≠ l' *)
      pose proof (reachability_dom _ _ _ H9).
      (* Key case analysis : is the modified value in the path ? *)
      eapply reachable_path_reachability in H9; light; flatten; subst; update_dom.
      * eapply B1; (try exists l0); simpl; eauto with rch.
      * pose proof H7.
        eapply reachable_path_assignment in H7 as [Hedge | Hpath]; eauto.
        ** eapply contains_edge_last_edge in Hedge; flatten.
           assert (σ2 ⊨ l' ⇝ l0). {
             eapply reachable_path_reachability.
             eapply contains_edge_split in Hedge0 ; flatten; eauto.
             rewrite Hedge2 in H9.
             eapply (reachable_path_app2 _ l' (l::p2) (l0::p1')) in H9.
             eapply reachable_path_assignment in H9; eauto.
             flatten; eauto with rch.
             exfalso; apply Hedge1.
             eapply contains_edge_last; eauto. }
           eapply C1; simpl; eauto with wf rch.
           exists l'; split => //.
        ** eapply B1; simpl; eauto.
           exists x; split; eauto using reachable_path_reachability.
           eapply reachable_path_reachability.
           right. eauto.
  - (* (σ1, L1) ⋖ (σ2', {l}) *)
    unfold scoping; simpl. intros.
    destruct H7; steps; inSingleton.
    eapply_anywhere storeSubset_singleton2.
    update_dom.
    destruct_eq (l = l'); subst.
    + (* if l = l', the assignment is weakening *)
      eapply H0; try (eexists; split);
        eauto using In_singleton, reachability_weaken_assignment with wf rch updates.
    + eapply reachable_path_reachability in H9; light; flatten; subst; update_dom.
      * eapply H0; try (eexists; split);
          eauto using In_singleton, reachability_weaken_assignment with wf rch updates.
      * pose proof H.
      (* Key case analysis : is the modified value in the path ? *)
        eapply reachable_path_assignment in H as [Hedge | Hpath]; eauto.
        ++ assert (l' < dom σ2). {
             erewrite <- update_dom.
             eapply reachability_dom2, reachable_path_is_reachable; eauto with rch.
             unfold contains_edge in Hedge; flatten.
             rewrite Hedge; apply in_app_iff; steps. }
           eapply H1; try (eexists; split); eauto using In_singleton with rch wf.
           eapply_anywhere contains_edge_last_edge; flatten.
           eapply reachable_path_reachability.
           destruct_eq (l' = l0); subst ; [left; split; eauto; lia | right ].
           eapply contains_edge_split in Hedge0 ; flatten; [steps | eauto].
           rewrite Hedge2 in H7.
           eapply (reachable_path_app2 _ l' (l::p2) (l0::p1')) in H7.
           eapply reachable_path_assignment in H7; eauto.
           flatten; eauto with rch.
           exfalso; apply Hedge1.
           eapply contains_edge_last; eauto.
        ++ eapply H0; try (eexists; split);
             eauto using In_singleton with wf rch updates.
           eapply reachable_path_reachability; eauto.
Qed.

(** ** Evaluation-maintained results *)
Global Hint Extern 1 => repeat rch_singleton: scp.
Global Hint Extern 1 => rewrite update_dom : updates.

(** ** Main Scopability theorem *)
(** We show the main theorem. As for wellformedness theorem, we have to make a custom proof. We use the results shown for initialization, lists and assignment *)
Theorem scopability_theorem:
  forall e σ ρ ψ v σ',
    ⟦e⟧p (σ, ρ, ψ) --> (v, σ') ->
    (codom ρ) ∪ {ψ} ⪽ σ -> wf σ ->
    ((σ, ((codom ρ) ∪ {ψ})) ⋖ (σ', {v})) /\ (σ ⇝ σ' ⋖ ((codom ρ) ∪ {ψ})) .
Proof with (timeout 10 eauto with scp wf rch lia).
  intros.
  move: H0 H1.
  induction H using evalP_ind2 with
    (Pl := fun _ σ ρ ψ vl σ' _ =>
             (codom ρ ∪ {ψ}) ⪽ σ ->
             wf σ ->
             ((σ, codom ρ ∪ {ψ}) ⋖ (σ', codom vl)) /\ (σ ⇝ σ' ⋖ (codom ρ ∪ {ψ})))
    (Pin := fun _ I ρ σ σ' _   => forall L σ0,
                dom σ0 <= dom σ ->
                (codom ρ ∪ {I}) ⪽ σ ->
                ((σ0, L) ⋖ (σ, (codom ρ) ∪ {I})) ->
                (σ0 ⇝ σ ⋖ L) ->
                wf σ ->
                ((σ0, L) ⋖ (σ', (codom ρ) ∪ {I})) /\ (σ0 ⇝ σ' ⋖ L));
    unfold assign, assign_new in * ; intros; eval_dom; eval_wf;
    try solve [rch_singleton; eauto with scp lia].
  - (* e = x *)
    unfold scoping; steps...
    exists l ...
  - (* e = e0.f *)
    unfold scoping; steps; rch_singleton ...
    assert ((σ,  (codom ρ) ∪ ({ψ})) ⋖ (σ1, {l})) as C1 by
        (eapply scp_trans with σ1 {l1}; eauto with updates rch wf scp).
    eapply C1 ; steps ...
  - (* e = e0.m(l0) *)
    destruct IHevalP1, IHevalP2; eauto with wf.
    destruct IHevalP3; eauto with wf.
    assert ((σ, (codom ρ) ∪ {ψ}) ⋖ (σ1, (codom ρ) ∪ {ψ})) as A4 by eauto with scp wf pM.
    assert ((σ, codom ρ ∪ {ψ}) ⋖ (σ2, (codom vl2) ∪ {v1}) ) as A6 by
        (eapply scp_union; eauto with scp wf pM lia).
    split.
    + eapply scp_trans with σ2 ( codom vl2 ∪ {v1}) ...
    + eapply scp_pr_trans with σ2 ( codom vl2 ∪ {v1}) ...
  - (* e = new C(l0) *)
    destruct IHevalP; eauto with wf.
    specialize IHevalP0 with (codom ρ ∪ {ψ}) σ.
    assert (dom σ1 <= dom (σ1 ++ [(C, [])])) by (rewrite dom_app; lia).
    destruct IHevalP0; eauto with wf .
    + rewrite dom_app ...
    + eapply storeSubset_union ...
      eapply storeSubset_singleton3 .
      rewrite dom_app ... (* storeSubset_add_empty ? *)
    + intros ? ; steps.
      move : H9 => [l0 [H__l0 H__rch]].
      inversion H__l0; steps.
      * eapply H3 ...
        eapply reachability_not_empty in H__rch ...
        exists l0; steps.
        eapply H_vals in H6 ...
      * inSingleton.
        eapply reachability_not_empty in H__rch as [ ] ...
        eapply reachability_dom2 in H6. lia.
    + eapply scp_pr_trans; eauto.
      unfold scoping_preservation; steps; eauto.
      unfold scoping; steps.
      move: H15 => [l0 [Hl0 H__rch]].
      eapply reachability_not_empty in H__rch as [ ]...
    + flatten; split => //.
      eapply scp_union_intror ; eauto with wf scp.
      eapply storeSubset_union.
      eapply storeSubset_trans; eauto with wf lia.
      eapply storeSubset_trans; eauto with wf lia.
      eapply storeSubset_singleton3 ...
      rewrite dom_app; lia.
  - (* e = e0.f = e1; e2 *)
    destruct (getObj σ2 v1) as [[C ω] |] eqn: H__obj.
    + destruct IHevalP1, IHevalP2 ...
      destruct IHevalP3; eauto with wf lia.
      * eapply storeSubset_trans with σ2; eauto with updates ...
      * eapply scp_assign with (f := x) (σ1 := σ) (l' := v2) (L1 := (codom ρ ∪ {ψ})) in H__obj as [ ];
          try reflexivity; eauto 5 with wf lia scp.
        split.
        -- eapply scp_trans with (σ2 := [v1 ↦ (C, [x ↦ v2] (ω))]σ2) (L2 := codom ρ ∪ {ψ});
             try eapply H8; eauto 3 with wf lia scp updates.
           eapply storeSubset_trans with σ2; eauto with updates wf lia.
        -- eapply scp_pr_trans; eauto with scp; update_dom ; eauto with wf lia.
           eapply_any; update_dom...
    + destruct IHevalP1, IHevalP2, IHevalP3 ...
      split .
      * eapply scp_trans with (σ2 := σ2) (L2 := codom ρ ∪ {ψ}) ...
      * eapply scp_pr_trans ...
  - (* el_nil *)
    split.
    + intros x; steps.
      inversion H3; steps.
    + eapply scp_pr_trans_degenerate ...
  - (* el_cons *)
    destruct IHevalP, IHevalP0 ...
    split.
    + rewrite codom_cons.
      eapply scp_union ...
    + eapply scp_pr_trans_degenerate ...
  - (* init_cons *)
    destruct IHevalP; eauto.
    destruct (getObj σ1 I) as [[C ω] |] eqn:H__obj; [| steps].
    inversion H__assign; subst.
    specialize (IHevalP0 L σ0).
    destruct IHevalP0; eauto with updates wf lia.
    + eapply scp_add_env ...
      eapply H3.
    + eapply scp_pr_trans; eauto.
      eapply scp_pr_trans; eauto.
      unfold scoping_preservation; intros ...
    + unfold wf; intros; update_dom.
      getObj_update; flatten; subst; repeat invert_constructor_equalities; subst; eauto.
      eapply getVal_add in H10; flatten; eauto with wf updates.
Qed.
