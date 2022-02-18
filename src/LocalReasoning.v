(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines the main result of local reasoning, built upon wellformedness, compatibility, scopability and stackability. In a wellformed, fully initialized context, a newly created object can only access hot (transitively fully initialized) locations. *)

From Celsius Require Export Scopability PartialMonotonicity Stackability MetaTheory.
Require Import ssreflect ssrbool Psatz Sets.Ensembles List Coq.Sets.Finite_sets_facts.
Import ListNotations.
Open Scope nat_scope.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc) (L: LocSet) (Σ: StoreTyping).

(** ** Local Reasoning theorem *)
(** We start with a lemma : *)
Lemma local_reasoning:
  forall σ σ' L L',
    L ⪽ σ ->
    L' ⪽ σ' ->
    wf σ' ->
    (σ, L) ⋖ (σ', L') ->
    σ ≪ σ' ->
    σ ⪯ σ' ->
    σ  ⊨ L  : hot ->
    σ' ⊨ L' : hot.
Proof.
  intros; intros l' H__l'.
    unfold dash_colon_, notation_reachability_mode, reachable_hot. intros l ?.
  assert (dom σ <= dom σ') by eauto with pM.
  destruct (PeanoNat.Nat.lt_ge_cases l (dom σ)).
  + (* l ∈ (dom σ) : the object was already in the store *)
    eapply pM_wf_warm_monotone; eauto.
    assert (σ ⊨ L ⇝ l).
    * eapply H2 ; simpl => //.
      exists l'; split; eauto with rch.
    * rch_set.
      eapply H5; eauto with rch.
  + (* l ∉ (dom σ) *)
    pose proof (rch_dom _ _ _ H6).
    destruct (H3 l); eauto with lia.
Qed.

(* Then the main theorem : *)
Theorem Local_reasoning:
  forall e σ ρ ψ v σ',
    ⟦e⟧(σ, ρ, ψ) --> (v, σ') ->
    wf σ ->
    (codom ρ ∪ {ψ}) ⪽ σ ->
    σ  ⊨ ((codom ρ) ∪ {ψ}) : hot ->
    σ' ⊨ v : hot.
Proof.
  intros.
  assert (σ' ⊨ (Singleton Loc v) : hot).
  + eapply local_reasoning;
      eauto using stk_theorem with pM stk wf lia.
    eapply scp_theorem in H; eauto with pM wf lia; steps.
  + eapply H3; eauto using In_singleton.
Qed.



(** ** Local reasoning *)

Axiom classicT : forall (P : Prop), {P} + {~ P}.

Lemma synchronization: forall Σ σ l,
    wf σ ->
    Σ ⊨ σ ->
    (forall (l': Loc), σ ⊨ l ⇝ l' -> Σ ⊨ l' : warm) ->
    exists Σ',
      (Σ' ⊨ σ) /\
        Σ ≼ Σ' /\
        Σ ▷ Σ' /\
        Σ ≪ Σ' /\
        (forall (l': Loc), σ ⊨ l ⇝ l' -> Σ' ⊨ l' : hot).
Proof with (meta; eauto with typ updates lia).

  Ltac getType_combine :=
    lazymatch goal with
    | H1: getType ?Σ ?l = Some ?T, H__st: ?Σ ⊨ ?σ
      |- context [getType (map ?f (combine (seq 0 (dom _)) ?Σ)) ?l ] =>
        try rewrite (proj1 H__st) ;
        rewrite /getType nth_error_map;
        rewrite (nth_error_nth' _  (0,(Entry,cold)));
        [rewrite combine_length seq_length PeanoNat.Nat.min_id ; auto |];
        rewrite ?combine_nth ?seq_nth ?seq_length; eauto with updates; simpl;
        rewrite (nth_error_nth _ _ _ H1)
    end.

  intros Σ σ l H__wf H__st; intros.
  remember ((fun l' '(C,μ) => if (classicT (σ ⊨ l ⇝ l')) then (C, hot) else (C, μ)):Loc -> Tpe -> Tpe) as f.
  remember (map (fun '(l, T) => f l T) (combine (seq 0 (dom Σ)) Σ)) as Σ'.
  exists Σ'.
  assert (Hyp: forall (A B C D E: Prop), ((D -> B -> A) /\ B /\ C /\ D /\ E) -> (A /\ B /\ C /\ D /\ E)) by firstorder.
  apply Hyp. clear Hyp.
  assert (H__dom: dom Σ' = dom Σ) by (subst; rewrite map_length combine_length seq_length; lia).
  splits.

  - intros H__stk H__mn. split; [rewrite (proj1 H__st) |]...
    intros l' H__l'. rewrite HeqΣ' in H__l'.
    rewrite map_length combine_length seq_length in H__l'... rewrite PeanoNat.Nat.min_id in H__l'.
    specialize ((proj2 H__st) l') as [C [ω [μ [? [? ?] ]]]] ...
    destruct (classicT (σ ⊨ l ⇝ l')) as [H__rch | H__nrch]; steps.
    + pose proof (H _ H__rch) ...
      exists C0, ω, hot; repeat split => //.
      * getType_combine. steps.
        inverts matched. Set Printing Coercions.
        destruct (classicT (σ ⊨ l ⇝ l')); steps.
      * destruct (ct C0) as [Args Flds Mtds] eqn:?.
        eapply ot_hot. eapply Heqc.
        intros f ?C ?μ. intros.
        assert (f < dom ω). {
          inverts H3; steps ...
          + (* warm *)
            inverts H4...
            lets (?C & ?ω & ?μ & ? & ? & ?): (proj2 H__st) l'...
            inverts H7.
            all: lets (v & ? & ?): H10 H5...
            apply getVal_dom in H0...
          + (* hot *)
            inverts H2...
            all: lets (v & ? & ?): H9 H5...
            apply getVal_dom in H2...
        }
        destruct (getVal ω f) eqn:?H__val ; [| apply nth_error_None in H__val; lia]...
        exists v; split => //.
        assert (σ ⊨ l ⇝ v) by (eapply rch_trans with l'; eauto with wf rch).
        exists (C, hot) ...
        lets: rch_dom H7.
        lets [ ]: getType_Some Σ v ...
        getType_combine.
        destruct (classicT (σ ⊨ l ⇝ v)); steps.
        assert (C1 = C); subst; eauto...
        inverts H2; meta...
        all: try lets [?v [ ] ]: H15 H5 ...
        all: try lets: H14 H5 ...
        all: try lets: H12 H5 ...
    + exists C, ω, μ; repeat split => // ...
      getType_combine; steps.
      destruct (classicT (σ ⊨ l ⇝ l')); steps.

  - intros l' H__l'.
    lets [?T ?]: getType_Some H__l'...
    exists (C, μ). subst...
    getType_combine.
    steps; eexists; steps.

  - intros l' C Ω H__l'.
    rewrite HeqΣ'.
    getType_combine. steps.
    destruct (classicT (σ ⊨ l ⇝ l')); steps.
    apply H in d. inverts d.
    inverts H0...
    inverts H4.

  - intros l' H__l'.
    right. rewrite <-H__dom...

  - intros l' H__rch.
    specialize (H l' H__rch) as [C H0].
    exists C, (C, hot); eauto with typ.
    inverts H0...
    erewrite HeqΣ'. getType_combine. steps.
    destruct (classicT (σ ⊨ l ⇝ l')); steps.
Qed.


Lemma local_reasoning2: forall Σ1 Σ2 σ1 σ2 L1 L2,
    L1 ⪽ σ1 ->
    L2 ⪽ σ2 ->
    (σ1, L1) ⋖ (σ2, L2) ->
    (Σ1 ≪ Σ2) ->
    (Σ1 ▷ Σ2) ->
    (Σ1 ≼ Σ2) ->
    (Σ1 ⊨ σ1) ->
    (Σ2 ⊨ σ2) ->
    (Σ1 ⊨ L1 : hot) ->
    wf σ1 ->
    wf σ2 ->
    exists Σ', (Σ2 ≪ Σ') /\
            (Σ2 ≼ Σ') /\
            (Σ2 ▷ Σ') /\
            (Σ' ⊨ σ2) /\
            (Σ' ⊨ L2 : hot).
Proof with (meta; eauto with typ lia).
  intros Σ1 Σ2 σ1 σ2 L1 L2 H1 H2.
  pose proof (storeSubset_finite _ _ H2).
  gen Σ1 Σ2 σ1 σ2 L1.
  eapply finite_sets_ind with (F := L2); intros.
  - exists Σ2; steps ...
    intros l Hl. inversion Hl.
  - clear H L2. rename F into L2, a into l.
    unfold Add in *.
    assert ((σ1, L1) ⋖ (σ2, L2)) by eauto with scp.
    pose proof (ss_union_l _ _ _ H2).
    lets [Σ3 [ ]]: H1 Σ2 H10; eauto; steps.
    (* clear Σ1 H5 H6 H7 H8 H10 H1. *) clear H1.
    lets [Σ4 [ ]]: synchronization Σ3 σ2 l H17; steps...

    + assert (l' < dom σ1 \/ l' >= dom σ1) as [|] by lia.
      * lets [l1 [H__l1 H__rch1]] : H4 H3 H2 l' H18; [ exists l; split; eauto with ss|].
        lets : H10 H__l1.  clear H10.
        lets: hot_transitivity H20 H__rch1...
        lets: mn_trans H7 H16.
        specialize (H22 l') as [?T1 [?T2 [? [ ]]]] ...
        exists C, (C,hot)...
      * lets: stk_st_trans H5 H14 H16.
        specialize (H20 l') as [ ]; eauto.
        -- apply rch_dom in H1.
           apply monotonicity_dom in H16.
           lets: (proj1 H9) ...
        -- lets: (proj1 H8) ...

    + exists Σ4; splits; eauto with typ.
      intros l0 [ l2' | ]; try inSingleton; eauto with rch wf typ.

  - apply H.
Qed.
