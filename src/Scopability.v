(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines the notions of scoping and scoping preservation. There are more complex and subtle, and should not serve as an introduction to the local reasonning properties.
The main idea is pretty natural: to ensure that newly created objects are hot, we need to check that, transitively, all locations reachable from the attributes of the object are intialized. To do so, we need to be able to reason about the set of locations that are reachable from a set of attributes in a given store. Given two stores [σ] and [σ'], and two sets of locations [L] and [L'], the pair [(σ, L)] "scopes" [(σ',L')] if all locations reachable from [L'] in [σ'] were already reachable from [L] in [σ].
 But as we allow to manipulate objects under initialization, we also need to consider a notion of "preservation" : scoping relations that are maintained when updating from one store to another. *)

From Celsius Require Export PartialMonotonicity Compatibility Wellformedness Reachability.
Require Import ssreflect ssrbool Psatz Sets.Ensembles List.
Import ListNotations.
Open Scope nat_scope.

(** ** Definitions and Notations *)
(* The scoping relation, with the hypothesis that the sets of locations are "correct" (within the stores) *)
Definition scoping (σ σ': Store) (L L': Ensemble Loc) :=
  L ⪽ σ ->
  L' ⪽ σ' ->
  (forall l, l < (dom σ) -> (σ' ⊫ L' ⇝ l) -> σ ⊫ L ⇝ l).
Notation "a ⋖ b" := (scoping (fst a) (fst b) (snd a) (snd b)) (at level 81).

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
Proof.
  unfold scoping, reachability_set; steps; eauto.
  eapply H => //.
  exists l'; steps; eauto with scoping.
  apply Union_intror; steps.
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
  unfold scoping, reachability_set; simpl; steps.
  eapply_any; eauto.
  eexists; eauto with scoping.
Qed.
Global Hint Resolve scoping_union_introl: scoping.

Lemma scoping_union_intror :
  forall σ1 σ2 L L1 L2,
    (L1 ∪ L2) ⪽ σ2 ->
    (σ1, L)  ⋖ (σ2, L1∪L2) ->
    (σ1, L)  ⋖ (σ2, L2).
Proof.
  unfold scoping, reachability_set; simpl; steps.
  eapply_any; eauto.
  eexists; eauto with scoping.
Qed.
Global Hint Resolve scoping_union_intror: scoping.


Lemma scoping_reachability:
  forall σ l1 l2,
    σ ⊨ l1 ⇝ l2 ->
    (σ, {l1}) ⋖ (σ, {l2}).
Proof.
  unfold scoping, reachability_set ; steps.
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
Proof.
  unfold scoping_preservation ; light; destructs.
  split; [eapply_any |]; light.
  eapply H4; eauto with wf lia.
  eapply scoping_transitivity with σ1 L1; eauto with wf lia rch.
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
  destruct H8; destructs.
  assert (s ⊨ x ⇝ l \/ ((s ⊨ x ⇝ I) /\ (s ⊨ v ⇝ l))) by
      eauto using reachability_add_env with updates.
  steps;
    [ eapply H4 | eapply H3] ;
    simpl; try (eexists; split); eauto with wf.
Qed.


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
  unfold scoping_preservation; light; destructs.
  split.
  - (* σ1 ⇝ σ2' ⋖ L1 *)
    split; eauto.
    move => σ0 L0 L H_dom1 H_dom2' H_subL H_subL0 A1 A2.
    intros. update_dom.
    unfold scoping; simpl.
    intros.
    assert ((σ0, L0) ⋖ (σ2, L)) as B1 by eauto.
    assert ((σ0, L0) ⋖ (σ2, {l'})) as C1 by eauto using scoping_transitivity.
    destruct H7; destructs.
    eapply storeSubset_update in H5.
    destruct_eq (l = l'); subst.
    + (* l = l' , the assignment is weakening *)
      eapply B1; simpl; (try exists x); eauto using reachability_weaken_assignment with wf.
    + (* l ≠ l' *)
      pose proof (reachability_dom _ _ _ H9).
      (* Key case analysis : is the modified value in the path ? *)
      eapply reachable_path_reachability in H9; light; destructs; subst; update_dom.
      * eapply B1; (try exists l0); simpl; eauto with rch.
      * pose proof H10.
        eapply reachable_path_assignment in H10 as [Hedge | Hpath]; eauto.
        ** eapply contains_edge_last_edge in Hedge; destructs.
           assert (σ2 ⊨ l' ⇝ l0). {
             eapply reachable_path_reachability.
             eapply contains_edge_split in Hedge0 ; destructs; eauto.
             rewrite Hedge2 in H9.
             eapply (reachable_path_app2 _ l' (l::p2) (l0::p1')) in H9.
             eapply reachable_path_assignment in H9; eauto.
             destructs; eauto with rch.
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
    + eapply reachable_path_reachability in H9; light; destructs; subst; update_dom.
      * eapply H0; try (eexists; split);
          eauto using In_singleton, reachability_weaken_assignment with wf rch updates.
      * pose proof H.
      (* Key case analysis : is the modified value in the path ? *)
        eapply reachable_path_assignment in H as [Hedge | Hpath]; eauto.
        ++ assert (l' < dom σ2). {
             erewrite <- update_dom.
             eapply reachability_dom2, reachable_path_is_reachable; eauto with rch.
             unfold contains_edge in Hedge; destructs.
             rewrite Hedge; apply in_app_iff; steps. }
           eapply H1; try (eexists; split); eauto using In_singleton with rch wf.
           eapply_anywhere contains_edge_last_edge; destructs.
           eapply reachable_path_reachability.
           destruct_eq (l' = l0); subst ; [left; split; eauto; lia | right ].
           eapply contains_edge_split in Hedge0 ; destructs; [steps | eauto].
           rewrite Hedge2 in H7.
           eapply (reachable_path_app2 _ l' (l::p2) (l0::p1')) in H7.
           eapply reachable_path_assignment in H7; eauto.
           destructs; eauto with rch.
           exfalso; apply Hedge1.
           eapply contains_edge_last; eauto.
        ++ eapply H0; try (eexists; split);
             eauto using In_singleton with wf rch updates.
           eapply reachable_path_reachability; eauto.
Qed.

(** ** Evaluation-maintained results *)
(** We start by defining the scopability property we want the evaluator to maintain. *)
Definition scopability_prop n :=
  forall e σ σ' ρ ψ l,
    ⟦e⟧(σ, ρ, ψ)(n) = (Success l σ') ->
    wf σ -> (codom ρ) ∪ {ψ} ⪽ σ ->
    ((σ, ((codom ρ) ∪ {ψ})) ⋖ (σ', {l})) /\ (σ ⇝ σ' ⋖ ((codom ρ) ∪ {ψ})) .

(* We show the induction case for lists *)
Lemma scopability_list_aux:
  forall n,
    (forall k, k < S n -> scopability_prop k) (**r strong induction hypothesis *) ->
    forall el σ ρ ψ  ρ' σ' ,
      (⟦_ el _⟧ (σ, ρ, ψ )(n)) = Success_l ρ' σ' ->
      wf σ ->
      (codom ρ ∪ {ψ}) ⪽ σ ->
      ((σ, codom ρ ∪ {ψ}) ⋖ (σ', codom ρ')) /\ (σ ⇝ σ' ⋖ codom ρ ∪ {ψ}).
Proof.
  unfold scopability_prop; intros.
  destruct n; try discriminate.
  simpl in * |- .
  (* We generalize the induction hypothesis *)
  assert (forall el ρ' σ1 σ2 acc,
             fold_left (eval_list_aux ρ ψ n) el (Success_l acc σ1) = Success_l ρ' σ2 ->
             wf σ1 ->
             dom σ <= dom σ1 ->
             σ ⇝ σ1 ⋖ (codom ρ ∪ {ψ}) ->
             (codom acc) ⪽ σ1 ->
             ((σ, codom ρ ∪ {ψ}) ⋖ (σ1, codom acc)) ->
             ((σ, codom ρ ∪ {ψ}) ⋖ (σ2, codom ρ')) /\
             (σ ⇝ σ2 ⋖ codom ρ ∪ {ψ}) /\
             codom ρ' ⪽ σ2) as H_ind. {
    induction el0; [solve [steps] |].
    intros L σ1 σ2 acc Hfold; intros.
    destruct n; simpl in Hfold; [rewrite_anywhere foldLeft_constant => // |].
    destruct_eval_with_name Heval.
    repeat eval_dom || eval_wf.
    eapply H in Heval; try lia; try destructs; eauto with wf.
    eapply IHel0 in Hfold; try rewrite codom_cons; eauto with scoping; try lia.
    + eauto with wf.
    + eapply scoping_union.
      ++ apply scoping_transitivity with σ1 (codom ρ ∪ {ψ});
           eauto with wf scoping.
      ++ apply Heval1; eauto with lia scoping.
  }
  eapply H_ind in H0; try erewrite codom_empty_union; steps; eauto with wf scoping.
  apply scoping_reflexivity.
  intros l'; steps. inversion H3.
Qed.

(** Then the induction case for initialization of a new object *)
Lemma scopability_init_aux:
  forall n,
    (forall k, k < S n -> scopability_prop k) (**r strong induction hypothesis *) ->
    forall σ L L1 I fields σ1 σ2,
      fold_left (init_field L1 I n) fields (Some σ1) = Some σ2 ->
      dom σ <= dom σ1 ->
      I < dom σ1 ->
      wf σ1 ->
      (codom L1 ∪ {I}) ⪽ σ1 ->
      ((σ, L) ⋖ (σ1, (codom L1) ∪ {I})) ->
      (σ ⇝ σ1 ⋖ L) ->

      ((σ, L) ⋖ (σ2, (codom L1) ∪ {I})) /\ (σ ⇝ σ2 ⋖ L) /\ (dom σ1 <= dom σ2).
Proof.
  unfold scopability_prop. intros n H_strong σ L L1 I.
  induction fields; [steps |]; intros; simpl in H.
  destruct n; [rewrite_anywhere foldLeft_constant => // |]; simpl in H.
  destruct a as [_ e]; destruct_eval.
  rewrite {2}/assign_new in H.
  destruct (getObj s I) eqn:G; try solve [rewrite_anywhere  foldLeft_constant => //].
  destruct o.
  eval_dom; eval_wf.
  eapply H_strong in H6; eauto with wf; destructs.
  eapply IHfields in H; eauto;
    destructs; repeat split;
      try update_dom; try lia;
        try solve [eapply_any; eauto];
        eauto with wf pM.
  ++ unfold wf; intros; update_dom.
     getObj_update; destructs; try invert_constructor_equalities; subst; eauto.
     eapply_anywhere getVal_add; destructs; eauto with wf updates.
  ++ eapply storeSubset_trans with s; update_dom; eauto with wf lia.
  ++ eapply scoping_transitivity with σ1 _; try solve [eapply_any]; eauto with scoping.
     apply scopability_add_env; eauto with wf lia.
     eapply_any; eauto with scoping.
  ++ intros.
     eapply preserving_transitivity; eauto.
     eapply preserving_transitivity; eauto.
     unfold scoping_preservation; split; intros; eauto using scopability_add_env with wf.
     update_dom; lia.
Qed.


(** ** Main Scopability theorem *)
(** We show the main theorem. As for wellformedness theorem, we have to make a custom proof. We use the results shown for initialization, lists and assignment *)
Theorem scopability_theorem:
  forall n, scopability_prop n.
Proof.
  apply strong_induction.
  intros n H_strong. unfold scopability_prop; intros.
  destruct n => //.
  destruct e as [x | this | e0 f | e0 m el | C el | e0 f e1 e2];
    simpl in H; repeat destruct_match;
      try discriminate;
      try (destruct n ; [discriminate |]);
      try invert_constructor_equalities; subst.
  + (* e = x *)
    unfold scoping; steps; try rch_singleton; eauto with scoping.
    eexists; split; eauto.
    eapply Union_introl, nth_error_In; eauto.
  + (* e = this *)
    unfold scoping; steps; try rch_singleton; eauto with scoping.
    eexists; eauto using Union_intror, In_singleton.
  + (* e = e0.f *)
    unfold scoping; intros; simpl.
    eval_dom; eval_wf.
    eapply H_strong in matched; try lia.
    intuition auto.
    assert ((σ', {v}) ⋖ (σ', {l})) as B1 by eauto with rch scoping updates.
    assert ((σ,  (codom ρ) ∪ ({ψ})) ⋖ (σ', {l})) as C1 by
          (eapply scoping_transitivity with σ' {v}; eauto with updates rch wf); steps.
  + (* e = e0.m(l0) *)
    rename s into σ0, l0 into ρ', v into l0, e into ω, matched0 into A5,
    s0 into σ_n, body into e_m, l into l_m, σ' into σ_m. (* Renaming for readability *)
    repeat eval_dom || eval_wf. (* We extract the wellformedness results of successful evaluations *)
    eapply H_strong in H, matched; try lia. (* We apply the induction hypothesis on sub evaluations *)
    eapply scopability_list_aux in matched6;
      try lia; eauto with wf ; destructs. (* We use the list induction case proven before *)
    assert ((codom ρ' ∪ {l0}) ⪽ σ_n) by eauto with wf.
    repeat destructs || modus_ponens.
    nat_le_trans.
    assert ((σ, (codom ρ) ∪ {ψ}) ⋖ (σ0, (codom ρ) ∪ {ψ})) as A4 by eauto with scoping wf pM.
    assert ((σ, codom ρ ∪ {ψ}) ⋖ (σ_n, (codom ρ') ∪ {l0}) ) as A6. {
      apply scoping_union.
       ++ eapply scoping_transitivity with σ0 _; eauto; eauto with wf lia.
       ++ eapply matched1; eauto with wf lia.
    }
    split; eauto with scoping.
  + (* e = new C(l0) *)
    rename matched into C0, s into σ_n, l0 into L.
    assert (dom σ <= dom σ_n) by eauto with pM.
    eval_wf.
    eapply scopability_list_aux in C0; eauto with wf; destructs.
    simpl in matched0. repeat (destruct_match; try discriminate).
    assert (dom (σ_n ++ [(C, [])]) = S (dom σ_n)) as H_dom
        by (unfold dom; rewrite app_length; simpl; lia).
    eapply scopability_init_aux with (σ := σ) (L := codom ρ ∪ {ψ}) in matched0;
      try rewrite H_dom; eauto with wf lia.
    ++ destructs; split => //.
       eapply scoping_union_intror ; eauto with wf scoping.
       fold (dom σ_n) in *. rewrite H_dom in matched3.
       apply storeSubset_union; eauto with wf lia.
       eapply storeSubset_trans with σ_n; eauto; lia.
    ++ eapply storeSubset_union.
       +++ eapply storeSubset_trans with σ_n ; eauto with wf lia.
       +++ eapply storeSubset_singleton3; unfold dom in * ; eauto with wf lia.
    ++ intros x ; steps.
       eapply_anywhere reachability_empty;
         unfold dom in * ; [| eauto using PeanoNat.Nat.lt_le_trans ].
       eapply C1; steps.
       inversion H4; steps. eexists.
       inversion H6; try inSingleton; steps; eauto.
       eapply reachability_dom2 in H7; exfalso; unfold dom in *; lia.
    ++ eapply preserving_transitivity; eauto.
       unfold scoping_preservation; split; intros; eauto.
       unfold scoping; simpl; intros.
       assert (reachability_set σ_n L1 l) by eauto using PeanoNat.Nat.lt_le_trans, reachability_empty.
       steps.
  + (* e = e0.f = e1; e2 *)
    rename matched into A0, s into σ0, v into l0, s0 into σ1, v0 into l1, matched0 into B0.
    repeat eval_dom || eval_wf.
    unfold assign in *;
      repeat destruct_match; try solve [eapply nth_error_None in matched; unfold dom in *; lia].
    update_dom.
    assert (wf [l0 ↦ (c, [f ↦ l1] (e))] (σ1)) by eauto with wf.
    eval_wf; [eapply storeSubset_trans with σ; update_dom; eauto with lia |].
    eapply H_strong in A0, B0, H; try lia; eauto; repeat modus_ponens || destructs.
    destruct H; eauto with wf.
    unfold assign in *.
    destruct H6; [eapply storeSubset_trans with σ1; update_dom; eauto with wf lia |].
    epose proof (scopability_assignment σ σ1 ([l0 ↦ (c, [f ↦ l1] (e))] (σ1)) (codom ρ ∪ {ψ}) l0 l1 f c e _ ).
    destruct H11; eauto.
    ++ eauto with scoping.
    ++ eapply_any; eauto with scoping lia wf.
    ++ eapply scoping_transitivity with _ (codom ρ ∪ {ψ}); eauto with wf.
       eapply H9; eauto with scoping.
    ++ split.
       +++ eapply scoping_transitivity with ([l0 ↦ (c, [f ↦ l1] (e))] (σ1)) (codom ρ ∪ {ψ});
             update_dom;
             eauto with wf lia.
           eapply storeSubset_trans; update_dom; eauto with wf lia.
           eapply_any; update_dom; eauto with scoping lia.
       +++ eapply preserving_transitivity; eauto with scoping; update_dom; eauto with wf lia.
           eapply_any; update_dom; eauto with scoping lia.
Qed.
