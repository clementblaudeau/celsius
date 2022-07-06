(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL & Inria 2020-2022 *)
(* ------------------------------------------------------------------------ *)
(** This file defines the notions of scoping and scoping preservation. There are more complex and
subtle, and should not serve as an introduction to the local reasonning properties.  The main idea
is pretty natural: to ensure that newly created objects are hot, we need to check that,
transitively, all locations reachable from the attributes of the object are intialized. To do so, we
need to be able to reason about the set of locations that are reachable from a set of attributes in
a given store. Given two stores [σ] and [σ'], and two sets of locations [L] and [L'], the pair [(σ,
L)] "scopes" [(σ',L')] if all locations reachable from [L'] in [σ'] were already reachable from [L]
in [σ].  But as we allow to manipulate objects under initialization, we also need to consider a
notion of "preservation" : scoping relations that are maintained when updating from one store to
another. *)
From Celsius Require Export  Wellformedness.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc) (L: LocSet) (el: list Expr).

(** ** Definitions and Notations *)
(* The scoping relation, with the hypothesis that the sets of locations are "correct" (within the stores) *)

Definition scopability σ σ' L L' :=
  L ⪽ σ ->
  L' ⪽ σ' ->
  (forall (l:Loc), l < dom σ -> (σ' ⊨ L' ⇝ l) -> σ ⊨ L ⇝ l).


Notation "( σ1 , L1 )  ⋖  ( σ2 , L2 )" := (scopability σ1 σ2 L1 L2) (at level 0).
Notation "( σ1 ,  { l } )  ⋖  ( σ2 , L2 )" := (scopability σ1 σ2 {l} L2) (at level 0).
Notation "( σ1 , L1 )  ⋖  ( σ2 ,  { l } )" := (scopability σ1 σ2 L1 {l}) (at level 0).
Notation "( σ1 ,  { l1 } )  ⋖  ( σ2 ,  { l2 } )" := (scopability σ1 σ2 {l1} {l2}) (at level 0).

Local Hint Unfold scopability : scp.
Local Hint Unfold reachability_set: scp.
Local Hint Resolve Union_introl: scp.
Local Hint Resolve Union_intror: scp.
Local Hint Resolve In_singleton: core.

(** ** Basic results *)
(** We first show a set of basic results about scopability. The premisses can sometime look a bit arbitrary, but they are actually fine-tuned *)
Lemma scp_refl :
  forall σ L, (σ, L) ⋖ (σ, L).
Proof.
  eauto with scp.
Qed.
Global Hint Resolve scp_refl: scp.

Lemma scp_refl2 :
  forall σ L1 L2, L2 ⊆ L1 -> (σ, L1) ⋖ (σ, L2).
Proof.
  unfold scopability. steps; rch_set.
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
  unfold scopability; steps ...
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
  unfold scopability; intros.
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
  unfold scopability; intros.
  inversion H4; steps...
Qed.
(* Global Hint Resolve scp_union_introl: scp. *)

Lemma scp_union_intror :
  forall σ1 σ2 L L1 L2,
    (L1 ∪ L2) ⪽ σ2 ->
    (σ1, L) ⋖ (σ2, L1∪L2) ->
    (σ1, L) ⋖ (σ2, L2).
Proof with (eauto with wf rch).
  unfold scopability; intros.
  inversion H4; steps...
Qed.
(* Global Hint Resolve scp_union_intror: scp. *)

Lemma scp_reachability:
  forall σ l1 l2,
    σ ⊨ l1 ⇝ l2 ->
    (σ, {l1}) ⋖ (σ, {l2}).
Proof with (eauto with rch).
  unfold scopability; intros; rch_set...
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
  intros; unfold scopability; simpl; intros.
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
  forall σ L l v f C ω,
    getObj σ l = Some (C, ω) ->
    (σ, L ∪ {v}) ⋖ ([l ↦ (C, [f ↦ v] (ω))]σ, L ∪ {v}).

Proof with (eauto with scp rch).
  unfold scopability; intros.
  destruct H3 as [l1 [H__l1 H__rch]].
  lets [? | [H__rch1 H__rch2 ]]: rch_asgn H__rch; eauto;
    eexists...
Qed.

Lemma scp_assign_new:
  forall σ σ' x v L C,
    wf σ ->
    assign_new C x v σ = Some σ' ->
    (σ, L ∪ {v}) ⋖ (σ', L ∪ {v}).
Proof with (eauto with scp rch).
  unfold scopability, assign_new; intros. steps.
  rewrite_anywhere PeanoNat.Nat.eqb_eq. subst.
  destruct H4 as [l1 [H__l1 H__rch]].
  lets [? | [H__rch1 H__rch2 ]]: rch_asgn_new H__rch; eauto;
    eexists...
Qed.
Global Hint Resolve scp_assign_new: scp.
(** ** Evaluation-maintained results *)

(** ** Main Scopability theorem *)
(** We show the main theorem. As for wellformedness theorem, we have to make a custom proof. We use
the results shown for initialization, lists and assignment *)
Theorem scp_theorem:

  (forall e σ ρ ψ v σ',
      ⟦e⟧p (σ, ρ, ψ) --> (v, σ') ->
      (codom ρ) ∪ {ψ} ⪽ σ -> wf σ ->
      forall L , L ⪽ σ -> (codom ρ ∪ {ψ}) ⊆ L -> (σ, L) ⋖ (σ', L ∪ {v})) /\

    (forall el σ ρ ψ vl σ',
         ⟦el⟧ (σ, ρ, ψ) --> (vl, σ') ->
         (codom ρ ∪ {ψ}) ⪽ σ ->
         wf σ ->
         (forall L, L ⪽ σ -> (codom ρ ∪ {ψ}) ⊆ L -> (σ, L) ⋖ (σ', L ∪ codom vl))) /\

    (forall C ψ x ρ σ σ',
        initP C ψ x ρ σ σ' ->
        wf σ ->
        (codom ρ ∪ {ψ}) ⪽ σ ->
        forall ω, getObj σ ψ = Some (C, ω) ->
             (forall L, L ⪽ σ -> (codom ρ ∪ {ψ}) ⊆ L -> (σ, L) ⋖ (σ', L))).

Proof with (rch_set; updates; eauto 3 with scp wf rch lia).

  apply evalP_multi_ind;
    unfold assign in * ; intros; eval_dom; eval_wf.

  - (* e = x *)
    apply scp_union...
    unfold scopability; steps ... ss.
    exists l; split; eauto using getVal_codom with ss.

  - (* e = this *)
    apply scp_union...
    unfold scopability; steps...
    exists ψ; split...

  - (* e = e.f *)
    intuition auto...
    lets: H5 L H2...
    unfold scopability; steps...
    apply H4...
    inverts H__ln...
    + exists l0...
    + exists v1; split... apply rch_trans with v...

  - (* e = e0.m(l0) *)
    assert ((codom vl2 ∪ {v1}) ⪽ σ2); ss...
    assert (((L ∪ {v1}) ∪ codom vl2) ⪽ σ2); ss... apply ss_trans with σ...
    intuition auto.
    unfold scopability; steps.
    apply H9...
    apply H10... intros ?...
    apply H11... intros ? [ ]...
    exists l0; split... inverts H__ln; eauto 6 using Union.

  - (* e = new C(l0) *)
    assert ((L ∪ {dom σ1}) ⪽ σ1 ++ [(C, [])]). { ss... apply ss_trans with σ1... }
    eapply scp_trans with σ1 (L ∪ codom vl__args)...
    eapply scp_trans with (σ1++[(C,[])]) (L ∪ codom vl__args ∪ {dom σ1})...
    + ss; updates; try lia; apply ss_trans with σ1...
    + intros ? ? l ? ?.
      apply rch_add_empty_set in H9 as [|]...
      lets: rch_dom2 H9.
      inverts H__ln; rch_set... exists l0...
    + intros ? ? l ? ?.
      eapply IH__init...
      * ss... apply ss_trans with σ1...
      * intros ? [ ]...
      * ss. apply ss_trans with σ1...
      * exists l0; split... inverts H__ln...

  - (* e = e0.f = e1; e2 *)
    destruct (getObj σ2 v1) as [[C ω] |] eqn: H__obj.
    + apply scp_trans with σ1 (L∪{v1})...
      assert (((L ∪ {v1}) ∪ {v2}) ⪽ σ2). { ss... apply ss_trans with σ... }
      apply scp_trans with σ2 ((L∪{v1})∪{v2})... { apply IH__e2... intros ? ... }
      assert ((((L ∪ {v1}) ∪ {v2}) ∪ {v3}) ⪽ σ3). { ss... apply ss_trans with σ... }
      apply scp_trans with σ3 (((L∪{v1})∪{v2})∪{v3})...
      * eapply scp_trans with ([v1 ↦ (C, [x ↦ v2] (ω))] (σ2)) ((L ∪ {v1}) ∪ {v2})...
        -- ss...  apply ss_trans with σ...
        -- apply scp_assign...
        -- apply IH__e'... ss... apply ss_trans with σ... intros ? ?; eauto using Union.
      * apply scp_refl2... intros ? [ ]; eauto using Union.
    + apply scp_trans with σ1 (L∪{v1})...
      assert (((L ∪ {v1}) ∪ {v2}) ⪽ σ2). { ss... apply ss_trans with σ... }
      apply scp_trans with σ2 ((L∪{v1})∪{v2})... { apply IH__e2... intros ? ... }
      assert ((((L ∪ {v1}) ∪ {v2}) ∪ {v3}) ⪽ σ3). { ss... apply ss_trans with σ... }
      apply scp_trans with σ3 (((L∪{v1})∪{v2})∪{v3})... {
        apply IH__e'... intros ? ?. eauto using Union.  }
      apply scp_refl2... intros ? [ ]; eauto using Union.

  - (* el = nil *)
    apply scp_refl2. intros ? [ ] ... inverts H3.

  - (* el = e::el *)
    rewrite codom_cons.
    eapply scp_trans with σ1 (L ∪ {v1})...
    (* Union associativity would simplify things *)
    unfold scopability; intros.
    apply IH__el... intros ? ...
    exists l0; split...
    inverts H__ln... inverts H9...

  - (* init_nil *)
    done...

  - (* init_cons *)
    lets: scp_assign_new L H__assign ...
    lets: assign_new_dom H__assign.
    apply scp_trans with σ1 (L ∪ {v})...
    apply scp_trans with σ3 (L ∪ {v})... {
      ss... apply ss_trans with σ1...
    }
    apply scp_trans with σ2 (L ∪ {v})...
    + eapply ss_trans with σ1 ...
    + lets: init_field H__init...
      lets H__pM: pM_theorem_expr H__e.
      lets H__pM1: pM_assign_new H__assign.
      lets (?ω & H__obj1 & ?): H__pM I H1.
      lets (?ω & H__obj2 & ?): H__pM1 I H__obj1.
      eapply IH__init; try eapply ss_trans with σ1 ...
      * eapply wf_assign_new...
      * intros ? ...
Qed.

Corollary scp_theorem_expr:
  forall e σ ρ ψ v σ',
    ⟦e⟧p (σ, ρ, ψ) --> (v, σ') ->
    (codom ρ) ∪ {ψ} ⪽ σ -> wf σ ->
    ((σ, (codom ρ) ∪ {ψ}) ⋖ (σ', {v})).
Proof.
  intros.
  lets (? & _ & _): scp_theorem.
  lets: H2 H (codom ρ ∪ {ψ}) H0; eauto.
  eval_dom; eval_wf.
  apply scp_trans with σ' ((codom ρ ∪ {ψ}) ∪ {v}); eauto 3 with scp.
  + apply H3; intros ?; eauto.
  + apply scp_refl2. intros ? []; eauto using Union.
Qed.

Corollary scp_theorem_init:
  forall C I x ρ σ σ',
    initP C I x ρ σ σ' ->
    wf σ ->
    (codom ρ ∪ {I}) ⪽ σ ->
    forall ω, getObj σ I = Some (C, ω) ->
         (σ, codom ρ ∪ {I}) ⋖ (σ', codom ρ ∪ {I}).
Proof.
  intros.
  lets (_ & _ & ?): scp_theorem.
  eapply H3; eauto.
  intros ? => //.
Qed.
