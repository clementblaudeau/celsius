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
  (forall l, l < (dom σ) -> (σ' ⊫ L' ⇝ l) -> σ ⊫ L ⇝ l).

Notation "( σ1 , L1 )  ⋖  ( σ2 , L2 )" := (scoping σ1 σ2 L1 L2) (at level 0).
Notation "( σ1 , { l } )  ⋖  ( σ2 , L2 )" := (scoping σ1 σ2 {l} L2) (at level 0).
Notation "( σ1 , L1 )  ⋖  ( σ2 , { l } )" := (scoping σ1 σ2 L1 {l}) (at level 0).
Notation "( σ1 , { l1 } )  ⋖  ( σ2 , { l2 } )" := (scoping σ1 σ2 {l1} {l2}) (at level 0).


(* Notation "a ⋖ b" := (scoping (fst a) (fst b) (snd a) (snd b)) (at level 81).*)

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
Notation "σ1 ⇝ σ2 ⋖ L" := (scoping_preservation σ1 σ2 L) (at level 81, σ2 at level 80, L at level 80).

Global Hint Unfold scoping : scoping.
Global Hint Unfold scoping_preservation : scoping.
Global Hint Unfold reachability_set: scoping.
Global Hint Resolve Union_introl: scoping.
Global Hint Resolve Union_intror: scoping.


(** ** Basic results *)
(** We first show a set of basic results about scoping. The premisses can sometime look a bit arbitrary, but they are actually fine-tuned *)

Lemma scoping_reflexivity :
  forall σ L1 L2, L2 ⊆ L1 -> (σ, L1) ⋖ (σ, L2).
Proof.
  unfold scoping, reachability_set; steps.
  exists l'; steps; eapply H => //.
Qed.
Global Hint Resolve scoping_reflexivity: scoping.

Lemma scoping_reflexivity2 :
  forall σ L, (σ, L) ⋖ (σ, L).
Proof.
  eauto with scoping.
Qed.
Global Hint Resolve scoping_reflexivity2: scoping.

Lemma scoping_subset :
  forall σ1 σ2 L L1 L2,
    (σ1, L1) ⋖ (σ2, L2∪L) ->
    L2∪L ⪽ σ2 ->
    (σ1, L1) ⋖ (σ2, L).
Proof with (eauto with scoping).
  unfold scoping, reachability_set; steps ...
Qed.
Global Hint Resolve scoping_subset: scoping.

Lemma scoping_union :
  forall σ1 σ2 L L1 L2,
    (σ1, L)  ⋖ (σ2, L1) ->
    (σ1, L)  ⋖ (σ2, L2) ->
    (σ1, L)  ⋖ (σ2, L1∪L2).
Proof.
  unfold scoping, reachability_set; steps.
  induction H4; steps; eauto with wf.
Qed.
Global Hint Resolve scoping_union: scoping.

Lemma scoping_union_introl :
  forall σ1 σ2 L L1 L2,
    (L1 ∪ L2) ⪽ σ2 ->
    (σ1, L) ⋖ (σ2, L1∪L2) ->
    (σ1, L) ⋖ (σ2, L1).
Proof.
  unfold scoping, reachability_set; steps.
  eauto with scoping.
Qed.
Global Hint Resolve scoping_union_introl: scoping.

Lemma scoping_union_intror :
  forall σ1 σ2 L L1 L2,
    (L1 ∪ L2) ⪽ σ2 ->
    (σ1, L)  ⋖ (σ2, L1∪L2) ->
    (σ1, L)  ⋖ (σ2, L2).
Proof.
  unfold scoping, reachability_set; steps.
  eauto with scoping.
Qed.
Global Hint Resolve scoping_union_intror: scoping.


Lemma scoping_reachability:
  forall σ l1 l2,
    σ ⊨ l1 ⇝ l2 ->
    (σ, {l1}) ⋖ (σ, {l2}).
Proof.
  unfold scoping, reachability_set ; steps.
  eauto with scoping.
  exists l1; try inSingleton; steps; eauto with scoping rch.
Qed.
Global Hint Resolve scoping_reachability: scoping.


Lemma scoping_transitivity:
  forall σ1 σ2 σ3 L1 L2 L3,
    dom σ1 <= dom σ2 ->
    L2 ⪽ σ2 ->
    (σ1, L1) ⋖ (σ2, L2) ->
    (σ2, L2) ⋖ (σ3, L3) ->
    (σ1, L1) ⋖ (σ3, L3).
Proof.
  unfold scoping; unfold reachability_set; simpl ; steps.
  eauto with scoping lia.
Qed.
Global Hint Resolve scoping_transitivity: scoping.

Lemma preserving_transitivity:
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
  eapply scoping_transitivity with σ1 L1 ...
Qed.
Global Hint Resolve preserving_transitivity: scoping.

Lemma preserving_regularity_degenerate:
  forall σ1 σ2 L,
    σ1 ⇝ σ2 ⋖ L ->
    (dom σ1) <= (dom σ2) ->
    (σ1, L) ⋖ (σ2, L).
Proof.
  unfold scoping_preservation, scoping; simpl; steps.
  eauto with scoping.
Qed.
Global Hint Resolve preserving_regularity_degenerate: scoping.

Lemma preserving_regularity:
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
Global Hint Resolve preserving_regularity: scoping.

Lemma preserving_transitivity_degenerate:
  forall σ1 σ2 σ3 L1 ,
    σ1 ⇝ σ2 ⋖ L1 ->
    dom σ1 <= dom σ2 ->
    σ2 ⇝ σ3 ⋖ L1 ->
    σ1 ⇝ σ3 ⋖ L1.
Proof.
  steps; eauto with scoping.
Qed.
Global Hint Resolve preserving_transitivity_degenerate: scoping.

Lemma scopability_add:
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
  rewrite H1; eauto with scoping.
Qed.

Lemma scopability_add_env:
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
  assert (s ⊨ x ⇝ l \/ ((s ⊨ x ⇝ I) /\ (s ⊨ v ⇝ l))) by
      eauto using reachability_add_env with updates.
  steps;
    [ eapply H4 | eapply H3] ;
    simpl; try (eexists; split); eauto with wf.
Qed.
Hint Resolve scopability_add_env: scoping.


(** ** Assignment results *)
(** We prove some specific results on scopability in the context of assignment. The key reasonning technique is to do a case analysis on the presence of the modified entry in the reachability path. *)

Lemma scopability_assignment:
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
    assert ((σ0, L0) ⋖ (σ2, {l'})) as C1 by eauto using scoping_transitivity.
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
Hint Extern 1 => repeat rch_singleton: scoping.
Hint Extern 1 => rewrite update_dom : updates.

(** ** Main Scopability theorem *)
(** We show the main theorem. As for wellformedness theorem, we have to make a custom proof. We use the results shown for initialization, lists and assignment *)
Theorem scopability_theorem:
  forall e σ ρ ψ v σ',
    ⟦e⟧p (σ, ρ, ψ) --> (v, σ') ->
    (codom ρ) ∪ {ψ} ⪽ σ -> wf σ ->
    ((σ, ((codom ρ) ∪ {ψ})) ⋖ (σ', {v})) /\ (σ ⇝ σ' ⋖ ((codom ρ) ∪ {ψ})) .
Proof with (timeout 10 eauto with scoping wf rch lia).
  intros.
  move: H0 H1.
  induction H using evalP_ind2 with
    (Pl := fun _ σ ρ ψ vl σ' _ =>
             (codom ρ ∪ {ψ}) ⪽ σ ->
             wf σ ->
             ((σ, codom ρ ∪ {ψ}) ⋖ (σ', codom vl)) /\ (σ ⇝ σ' ⋖ codom ρ ∪ {ψ}))
    (Pin := fun _ ψ ρ σ σ' _   => forall L σ0,
                dom σ0 <= dom σ ->
                (codom ρ ∪ {ψ}) ⪽ σ ->
                ((σ0, L) ⋖ (σ, (codom ρ) ∪ {ψ})) ->
                (σ0 ⇝ σ ⋖ L) ->
                wf σ ->
                ((σ0, L) ⋖ (σ', (codom ρ) ∪ {ψ})) /\ (σ0 ⇝ σ' ⋖ L));
    unfold assign, assign_new in * ; intros; eval_dom; eval_wf;
    try solve [rch_singleton; eauto with scoping lia].
  - (* e = x *)
    unfold scoping; steps...
    exists l ...
  - (* e = e0.f *)
    unfold scoping; steps; rch_singleton ...
    assert ((σ,  (codom ρ) ∪ ({ψ})) ⋖ (σ1, {l})) as C1 by
        (eapply scoping_transitivity with σ1 {l1}; eauto with updates rch wf scoping).
    eapply C1 ; steps ...
  - (* e = e0.m(l0) *)
    destruct IHevalP1, IHevalP2; eauto with wf.
    destruct IHevalP3; eauto with wf.
    assert ((σ, (codom ρ) ∪ {ψ}) ⋖ (σ1, (codom ρ) ∪ {ψ})) as A4 by eauto with scoping wf pM.
    assert ((σ, codom ρ ∪ {ψ}) ⋖ (σ2, (codom vl2) ∪ {v1}) ) as A6 by
        (eapply scoping_union; eauto with scoping wf pM lia).
    split.
    + eapply scoping_transitivity with σ2 ( codom vl2 ∪ {v1}) ...
    + eapply preserving_transitivity with σ2 ( codom vl2 ∪ {v1}) ...
  - (* e = new C(l0) *)
    destruct IHevalP; eauto with wf.
    specialize IHevalP0 with (codom ρ ∪ {ψ}) σ.
    assert (dom σ1 <= dom (σ1 ++ [(C, [])])) by (rewrite dom_app; lia).
    destruct IHevalP0; eauto with wf .
    + rewrite dom_app. steps.
    + eapply storeSubset_union ...
      eapply storeSubset_singleton3 .
      rewrite dom_app ... (* storeSubset_add_empty ? *)
    + intros ? ; steps.
      move : H9 => [l0 [H__l0 H__rch]].
      inversion H__l0; steps.
      * eapply H3 ...
        eapply reachability_empty with (C := C) ...
      * inSingleton.
        eapply reachability_not_empty in H__rch ...
    + eapply preserving_transitivity; eauto.
      unfold scoping_preservation; steps; eauto.
      unfold scoping; steps.
      eapply reachability_empty in H15 ...
    + flatten; split => //.
       eapply scoping_union_intror ; eauto with wf scoping.
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
      * eapply scopability_assignment with (f := x) (σ1 := σ) (l' := v2) (L1 := (codom ρ ∪ {ψ})) in H__obj as [ ];
          try reflexivity; eauto 5 with wf lia scoping.
        split.
        -- eapply scoping_transitivity with (σ2 := [v1 ↦ (C, [x ↦ v2] (ω))]σ2) (L2 := codom ρ ∪ {ψ});
             try eapply H8; eauto 3 with wf lia scoping updates.
           eapply storeSubset_trans with σ2; eauto with updates wf lia.
        -- eapply preserving_transitivity; eauto with scoping; update_dom ; eauto with wf lia.
           eapply_any; update_dom...
    + destruct IHevalP1, IHevalP2, IHevalP3 ...
      split .
      * eapply scoping_transitivity with (σ2 := σ2) (L2 := codom ρ ∪ {ψ}) ...
      * eapply preserving_transitivity ...
  - (* el_nil *)
    split.
    + intros x; steps.
      inversion H3; steps.
    + eapply preserving_transitivity_degenerate ...
  - (* el_cons *)
    destruct IHevalP, IHevalP0 ...
    split.
    + rewrite codom_cons.
      eapply scoping_union ...
    + eapply preserving_transitivity_degenerate ...
  - (* init_cons *)
    destruct IHevalP; eauto.
    destruct (getObj σ1 I) as [[C ω] |] eqn:H__obj; [| steps].
    inversion H__assign; subst.
    specialize (IHevalP0 L σ0).
    destruct IHevalP0; eauto with updates wf lia.
    + eapply scopability_add_env ...
      eapply H3.
    + eapply preserving_transitivity; eauto.
      eapply preserving_transitivity; eauto.
      unfold scoping_preservation; intros ...
    + unfold wf; intros; update_dom.
      getObj_update; flatten; subst; repeat invert_constructor_equalities; subst; eauto.
      eapply getVal_add in H10; flatten; eauto with wf updates.
Qed.
