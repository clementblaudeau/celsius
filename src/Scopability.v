(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines the notions of scoping and scoping preservation. There are more complex and subtle, and should not serve as an introduction to the local reasonning properties.
The main idea is pretty natural: to ensure that newly created objects are hot, we need to check that, transitively, all locations reachable from the attributes of the object are intialized. To do so, we need to be able to reason about the set of locations that are reachable from a set of attributes in a given store. Given two stores [σ] and [σ'], and two sets of locations [L] and [L'], the pair [(σ, L)] "scopes" [(σ',L')] if all locations reachable from [L'] in [σ'] were already reachable from [L] in [σ].
 But as we allow to manipulate objects under initialization, we also need to consider a notion of "preservation" : scoping relations that are maintained when updating from one store to another. *)
From Celsius Require Export PartialMonotonicity Wellformedness Reachability Tactics.
Require Import ssreflect ssrbool Psatz Sets.Ensembles List.
Import ListNotations.
Open Scope nat_scope.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc) (L: LocSet).


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
  unfold scoping. steps; rch_set.
  exists l0; steps; eapply H => //.
Qed.
Global Hint Resolve scp_refl2: scp.
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
Global Hint Resolve scp_subset: scp.
Lemma scp_union :
  forall σ1 σ2 L L1 L2,
    (σ1, L)  ⋖ (σ2, L1) ->
    (σ1, L)  ⋖ (σ2, L2) ->
    (σ1, L)  ⋖ (σ2, L1∪L2).
Proof.
  autounfold with notations scp. steps.
  inversion H4; steps; eauto with wf.
Qed.
Global Hint Resolve scp_union: scp.
Lemma scp_union_introl :
  forall σ1 σ2 L L1 L2,
    (L1 ∪ L2) ⪽ σ2 ->
    (σ1, L) ⋖ (σ2, L1∪L2) ->
    (σ1, L) ⋖ (σ2, L1).
Proof.
  autounfold with notations scp ; steps.
  eauto with scp.
Qed.
Global Hint Resolve scp_union_introl: scp.
Lemma scp_union_intror :
  forall σ1 σ2 L L1 L2,
    (L1 ∪ L2) ⪽ σ2 ->
    (σ1, L)  ⋖ (σ2, L1∪L2) ->
    (σ1, L)  ⋖ (σ2, L2).
Proof.
  autounfold with notations scp ; steps.
  eauto with scp.
Qed.
Global Hint Resolve scp_union_intror: scp.

Lemma scp_reachability:
  forall σ l1 l2,
    σ ⊨ l1 ⇝ l2 ->
    (σ, {l1}) ⋖ (σ, {l2}).
Proof.
  autounfold with notations scp ; steps.
  exists l1; try inSingleton; steps; eauto with scp rch.
  eapply rch_trans; eauto.
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
      eauto using reachability_add_env with lia updates.
  steps;
    [ eapply H4 | eapply H3] ;
    simpl; try (eexists; split); eauto with ss.
Qed.
Global Hint Resolve scp_add_env: scp.

Lemma reachability_not_empty: forall σ C l1 l2,
    wf σ ->
    (σ++[(C, [])]) ⊨ l1 ⇝ l2 ->
    (l1 = dom σ /\ l2 = dom σ) \/ ( σ ⊨ l1 ⇝ l2).
Proof with (updates; eauto with wf rch lia).
  intros.
  remember (σ++[(C,[])]) as σ0.
  induction H0; steps ...
  - destruct (Lt.le_lt_or_eq _ _ H0); steps ...
  - eapply getObj_last_empty in H1; steps ...
Qed.

Lemma reachability_add_empty: forall σ C L l,
    wf σ ->
    (σ++[(C, [])]) ⊨ L ⇝ l ->
    (σ ⊨ L ⇝ l) \/ l = length σ.
Proof.
  intros.
  inversion H0 as [l1 [Hl1 Hrch]].
  eapply reachability_not_empty in Hrch; steps.
  left. exists l1; eauto.
Qed.

(** ** Assignment results *)
(** We prove some specific results on scopability in the context of assignment. The key reasonning technique is to do a case analysis on the presence of the modified entry in the reachability path. *)
Reset Ltac Profile.
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
    intros. updates.
    unfold scoping; simpl.
    intros.
    assert ((σ0, L0) ⋖ (σ2, L)) as B1 by eauto.
    assert ((σ0, L0) ⋖ (σ2, {l'})) as C1 by eauto using scp_trans.
    destruct H7; steps.
    eapply ss_update in H5.
    destruct_eq (l = l'); subst.
    + (* l = l' , the assignment is weakening *)
      eapply B1; simpl; (try exists x); eauto using reachability_weaken_assignment with wf.
    + (* l ≠ l' *)
      pose proof (reachability_dom _ _ _ H9).
      (* Key case analysis : is the modified value in the path ? *)
      eapply reachable_path_reachability in H9; light; flatten; subst; updates.
      * eapply B1; (try exists l0); simpl; eauto with rch.
      * pose proof H7.
        eapply reachable_path_assignment in H7 as [Hedge | Hpath]; eauto.
        ** eapply contains_edge_last_edge in Hedge; flatten.
           assert (σ2 ⊨ l' ⇝ l0). {
             eapply reachable_path_reachability.
             eapply contains_edge_split in Hedge0 ; flatten; eauto.
             rewrite H10 in H9.
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
    destruct H7; steps; inSingleton. ss; updates.
    destruct_eq (l = l'); subst.
    + (* if l = l', the assignment is weakening *)
      eapply H0; try (eexists; split);
        eauto using In_singleton, reachability_weaken_assignment with wf rch updates.
    + eapply reachable_path_reachability in H9; light; flatten; subst; updates.
      * eapply H0; try (eexists; split);
          eauto using In_singleton, reachability_weaken_assignment with wf rch updates.
      * pose proof H.
      (* Key case analysis : is the modified value in the path ? *)
        eapply reachable_path_assignment in H as [Hedge | Hpath]; eauto.
        ++ assert (l' < dom σ2). {
             unfold contains_edge in Hedge; flatten.
             apply reachable_path_is_reachable with (l := l') in H7.
             eapply reachability_dom2 in H7; updates => //.
             rewrite Hedge; apply in_app_iff; steps. }
           eapply H1; try (eexists; split); eauto using In_singleton with rch wf.
           eapply_anywhere contains_edge_last_edge; flatten.
           eapply reachable_path_reachability.
           destruct_eq (l' = l0); subst ; [left; split; eauto; lia | right ].
           eapply contains_edge_split in Hedge0 ; flatten; [steps | eauto].
           rewrite H9 in H7.
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


(** ** Main Scopability theorem *)
(** We show the main theorem. As for wellformedness theorem, we have to make a custom proof. We use the results shown for initialization, lists and assignment *)
Theorem scp_theorem:
  forall e σ ρ ψ v σ',
    ⟦e⟧p (σ, ρ, ψ) --> (v, σ') ->
    (codom ρ) ∪ {ψ} ⪽ σ -> wf σ ->
    ((σ, (codom ρ) ∪ {ψ}) ⋖ (σ', {v})) /\ (σ ⇝ σ' ⋖ (codom ρ) ∪ {ψ}) .
Proof with (rch_set; updates; timeout 10 eauto with scp wf rch lia).
  intros.
  move: H0 H1.
  induction H using evalP_ind2 with
    (Pl := fun _ σ ρ ψ vl σ' _ =>
             (codom ρ ∪ {ψ}) ⪽ σ ->
             wf σ ->
             ((σ, codom ρ ∪ {ψ}) ⋖ (σ', codom vl)) /\ (σ ⇝ σ' ⋖ (codom ρ ∪ {ψ})))
    (Pin := fun C flds I ρ σ σ' _   => forall L σ0 Args Flds Mtds ω,
                (* Hypothesis *)
                wf σ ->
                (codom ρ ∪ {I}) ⪽ σ ->
                ct C = class Args Flds Mtds ->
                getObj σ I = Some (C, ω) ->
                dom ω + dom flds = dom Flds ->
                ((σ0, L) ⋖ (σ, (codom ρ) ∪ {I})) ->
                (σ0 ⇝ σ ⋖ L) ->
                dom σ0 <= dom σ ->
                (* Conclusions *)
                ((σ0, L) ⋖ (σ', (codom ρ) ∪ {I})) /\
                  (σ0 ⇝ σ' ⋖ L) /\
                  (exists ω', getObj σ' I = Some (C, ω') /\ dom ω' = dom Flds));
    unfold assign, assign_new in * ; intros; eval_dom; eval_wf.
  - (* e = x *)
    unfold scoping; steps ... ss.
    exists l; split; eauto using getVal_codom with ss.
  - (* this *)
    split...
  - (* e = e0.f *)
    unfold scoping; steps; rch_set; ss.
    assert ((σ,  (codom ρ) ∪ ({ψ})) ⋖ (σ1, {l})) as C1.
    + eapply scp_trans with σ1 {l1}; eauto with wf.
      unfold scoping; steps. rch_set.
      eapply rch_trans_n with v1; eauto with rch.
    + eapply C1 ; steps ...
  - (* e = e0.m(l0) *)
    destruct IHevalP1, IHevalP2; eauto with wf.
    destruct IHevalP3; eauto with ss lia.
    assert ((σ, (codom ρ) ∪ {ψ}) ⋖ (σ1, (codom ρ) ∪ {ψ})) as A4 by eauto with scp wf pM.
    assert ((σ, codom ρ ∪ {ψ}) ⋖ (σ2, (codom vl2) ∪ {v1}) ) as A6 by
        (eapply scp_union; eauto with scp wf pM lia).
    split.
    + eapply scp_trans with σ2 ( codom vl2 ∪ {v1}) ...
    + eapply scp_pr_trans with σ2 ( codom vl2 ∪ {v1}) ...
  - (* e = new C(l0) *)
    destruct IHevalP; eauto with wf.
    specialize IHevalP0 with (codom ρ ∪ {ψ}) σ Args Flds Mtds [].
    assert (dom σ1 <= dom (σ1 ++ [(C, [])])); updates; try lia.
    destruct IHevalP0 as [ ? [ ]]; eauto with wf lia.
    + ss... eapply ss_trans with σ1...
    + intros ? ; steps.
      move : H9 => [l0 [H__l0 H__rch]].
      inversion H__l0; steps.
      * eapply H3 ...
        eapply reachability_not_empty in H__rch ...
        exists l0; steps.
        eapply H_vals in H6 ...
      * inSingleton.
        eapply reachability_not_empty in H__rch; steps; try lia.
        eapply reachability_dom2 in H6. lia.
    + eapply scp_pr_trans; eauto.
      unfold scoping_preservation; steps; eauto.
      unfold scoping; steps.
      move: H15 => [l0 [Hl0 H__rch]].
      eapply reachability_not_empty in H__rch; steps; try lia.
      apply H11 ... exists l0 ...
    + flatten; split => //.
      eapply scp_union_intror ; eauto with wf scp. ss...
      eapply ss_trans with σ1...
  - (* e = e0.f = e1; e2 *)
    destruct (getObj σ2 v1) as [[C ω] |] eqn: H__obj.
    + destruct IHevalP1; eauto.
      destruct IHevalP2; eauto with wf lia.
      destruct IHevalP3; eauto with wf lia.
      eapply scp_assign with (f := x) (σ1 := σ) (l' := v2) (L1 := (codom ρ ∪ {ψ})) in H__obj as [ ];
          try reflexivity; eauto 3 with wf lia scp; [split |].
      * eapply scp_trans with (σ2 := [v1 ↦ (C, [x ↦ v2] (ω))]σ2) (L2 := codom ρ ∪ {ψ});
             try eapply H8; eauto 3 with wf lia scp updates.
      * eapply scp_pr_trans_degenerate with (σ2 := [v1 ↦ (C, [x ↦ v2] (ω))] (σ2)) ; eauto with scp lia...
      * eapply H10...
    + destruct IHevalP1; eauto.
      destruct IHevalP2; eauto with wf lia.
      destruct IHevalP3; eauto with wf lia.
      split .
      * eapply scp_trans with (σ2 := σ2) (L2 := codom ρ ∪ {ψ}) ...
      * eapply scp_pr_trans ...
  - (* el_nil *)
    split.
    + intros x; steps.
      inversion H3; steps.
    + eapply scp_pr_trans_degenerate ...
  - (* el_cons *)
    destruct IHevalP; eauto.
    destruct IHevalP0; eauto with wf lia.
    split.
    + rewrite codom_cons.
      eapply scp_union.
      * apply H7; eauto with lia wf scp.
      * eapply scp_trans with (σ2 := σ1) (L2 := codom ρ ∪ {ψ}) ...
    + eapply scp_pr_trans_degenerate ...
  - (* init_nil *)
    steps ...
  - (* init_cons *)
    destruct IHevalP; eauto.
    lets [?ω [ ]]: eM_theorem H H3; cross_rewrites.
    rewrite H12 in H__assign. inverts H__assign.
    specialize (IHevalP0 L σ0 Args Flds Mtds (ω0++[v])).
    simpl in H4.
    destruct IHevalP0 as [ ? [ ]]; updates; eauto with updates wf lia.
    + eapply scp_add_env; eauto with lia wf; updates.
      * apply H6.
      * eapply scp_trans ...
      * eapply scp_trans ...
    + eapply scp_pr_trans; eauto.
      eapply scp_pr_trans; eauto.
      unfold scoping_preservation; intros ...
Qed.

Corollary scp_theorem_init:
  forall C flds I ρ σ σ',
    initP C flds I ρ σ σ' ->
    forall L σ0 Args Flds Mtds ω,
      (* Hypothesis *)
      wf σ ->
      (codom ρ ∪ {I}) ⪽ σ ->
      ct C = class Args Flds Mtds ->
      getObj σ I = Some (C, ω) ->
      dom ω + dom flds = dom Flds ->
      ((σ0, L) ⋖ (σ, (codom ρ) ∪ {I})) ->
      (σ0 ⇝ σ ⋖ L) ->
      dom σ0 <= dom σ ->
      (* Conclusions *)
      ((σ0, L) ⋖ (σ', (codom ρ) ∪ {I})) /\
        (σ0 ⇝ σ' ⋖ L) /\
        (exists ω', getObj σ' I = Some (C, ω') /\ dom ω' = dom Flds).
Proof with (rch_set; updates; timeout 10 eauto with scp wf rch lia).
  introv H.
  induction H; intros.
  - splits...
    simpl in *.
    exists ω; split...
  - lets [ ]: scp_theorem H; eauto. unfold assign_new in H0. eval_dom; eval_wf.
    lets [?ω [ ]]: eM_theorem H H5; cross_rewrites.
    rewrite H14 in H0. inverts H0.
    specialize (IHinitP L σ0 Args Flds Mtds (ω0++[v])).
    simpl in *. updates.
    destruct IHinitP as [ ? [ ]]; updates; eauto with updates wf lia.
    + eapply scp_add_env; eauto with lia wf; updates.
      * apply H8.
      * eapply scp_trans ...
      * eapply scp_trans ...
    + eapply scp_pr_trans; eauto.
      eapply scp_pr_trans; eauto.
      unfold scoping_preservation; intros ...
Qed.
