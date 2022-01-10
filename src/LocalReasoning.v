(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines the main result of local reasoning, built upon wellformedness, compatibility, scopability and stackability. In a wellformed, fully initialized context, a newly created object can only access hot (transitively fully initialized) locations. *)

From Celsius Require Export Scopability Compatibility PartialMonotonicity Stackability MetaTheory.
Require Import ssreflect ssrbool Psatz Sets.Ensembles List Coq.Sets.Finite_sets_facts.
Import ListNotations.
Open Scope nat_scope.

(** ** Local Reasoning theorem *)
(** We start with a lemma : *)
Lemma local_reasoning:
  forall (σ σ': Store) (L L': LocSet),
    L ⪽ σ ->
    L' ⪽ σ' ->
    (σ, L) ⋖ (σ', L') ->
    σ ≪ σ' ->
    σ ⪨ σ' ->
    σ ⪯ σ' ->
    σ  ⊨ L  : hot ->
    σ' ⊨ L' : hot.
Proof.
  intros; intros l' H__l'.
    unfold dash_colon_, notation_reachability_mode, reachable_hot. intros l ?.
  assert (dom σ <= dom σ') by eauto with pM.
  destruct (PeanoNat.Nat.lt_ge_cases l (dom σ)).
  + (* l ∈ (dom σ) : the object was already in the store *)
    eapply pM_warm_monotone; eauto.
    assert (σ ⊨ L ⇝ l).
    * eapply H1 ; simpl => //.
      exists l'; split; eauto with rch.
    * rch_set.
      eapply H5; eauto with rch.
  + (* l ∉ (dom σ) *)
    pose proof (reachability_dom _ _ _ H6).
    destruct (H2 l); eauto with lia.
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
      eauto using stk_theorem with pM stk cmpt wf lia.
    eapply scopability_theorem in H; eauto with pM wf lia; steps.
  + eapply H3; eauto using In_singleton.
Qed.



(** ** Local reasoning *)
Parameter reachabilityb : Store -> Loc -> Loc -> bool.
Parameter reachability_refl: forall σ l l', Bool.reflect (reachability σ l l') (reachabilityb σ l l').

Lemma reachabilityb_true:
  forall σ l l',
    (σ ⊨ l ⇝ l') <-> (reachabilityb σ l l' = true).
Proof.
  intros.
  destruct (reachability_refl σ l l'); steps.
Qed.

Lemma reachabilityb_false:
  forall σ l l',
    (~ (σ ⊨ l ⇝ l')) <-> (reachabilityb σ l l' = false).
Proof.
  intros.
  destruct (reachability_refl σ l l'); steps.
Qed.

Lemma synchronization: forall Σ σ (l: Loc),
    wf σ ->
    Σ ⊨ σ ->
    (forall (l': Loc), σ ⊨ l ⇝ l' -> Σ ⊨ l' : warm) ->
    exists Σ',
      (Σ' ⊨ σ) /\
        Σ ≼ Σ' /\
        Σ ▷ Σ' /\
        Σ ≪ Σ' /\
        (forall (l': Loc), σ ⊨ l ⇝ l' -> Σ' ⊨ l' : hot).
Proof with (meta; eauto with typ).
  intros Σ σ l H__wf H__st; intros.
  remember ((fun l' '(C,μ) => if (reachabilityb σ l l') then (C, hot) else (C, μ)):Loc -> Tpe -> Tpe) as f.
  remember (map (fun '(l, T) => (l, f l T)) Σ) as Σ'.
  exists Σ'.
  assert (Hyp: forall (A B C D E: Prop), ((D -> B -> A) /\ B /\ C /\ D /\ E) -> (A /\ B /\ C /\ D /\ E)) by firstorder.
  apply Hyp. clear Hyp.
  repeat split.
  - intros H__stk H__mn l' H__l'. rewrite HeqΣ' in H__l'.
    apply in_dom_map in H__l'...
    specialize (H__st l' H__l') as [C [ω [μ [? [? ?] ]]]] ...
    destruct (reachability_refl σ l l'); steps.
    + pose proof (H _  r) ...
      exists C0, ω, hot; repeat split => //.
      * apply reachabilityb_true in r.
        erewrite getType_map; steps; eauto.
        inverts matched. reflexivity.
      * inverts H4; meta; eauto with typ.
        apply ot_hot; intros f v H__val.
        assert (σ ⊨ l ⇝ v) by eauto with rch.
        assert (Σ ⊨ v : warm) by eauto.
        inverts H4. inverts H6 ...
        exists x, (x, hot) ...
        erewrite getType_map ...
        destruct (reachability_refl σ l v); steps.
    + exists C, ω, μ; repeat split => // ...
      erewrite getType_map ...
      destruct (reachability_refl σ l l'); steps.
  - intros l' H__l'.
    destruct (getType Σ l') as [T1 |] eqn:?; [|exfalso; apply getType_none in Heqo; eauto].
    exists T1. subst.
    erewrite getType_map; eauto. steps; eexists; steps.
  - intros l' C Ω H__l'.
    erewrite HeqΣ', getType_map; eauto. steps.
    destruct (reachability_refl σ l l'); steps.
    apply H in r.
    inverts r.
    inverts H0 ...
    inverts H4.
  - intros l' H__l'.
    right.
    destruct (getType (map (fun '(l, T) => (l, f l T)) Σ) l')
      as [[C μ] |] eqn:?; [| eapply getType_none in Heqo; steps].
    eapply getType_in_dom_map; eauto.
  - intros l' H__rch.
    specialize (H l' H__rch) as [C H0].
    exists C, (C, hot); eauto with typ.
    inverts H0; meta.
    erewrite HeqΣ', getType_map; eauto. steps.
    destruct (reachability_refl σ l l'); steps.
Qed.




Lemma local_reasoning2: forall Σ1 Σ2 σ1 σ2 (L1 L2: LocSet),
    L1 ⪽ σ1 ->
    L2 ⪽ σ2 ->
    (σ1, L1) ⋖ (σ2, L2) ->
    (Σ1 ≪ Σ2) ->
    (Σ1 ▷ Σ2) ->
    (Σ1 ≼ Σ2) ->
    (Σ1 ⊨ σ1) ->
    (Σ2 ⊨ σ2) ->
    (Σ1 ⊨ L1 : hot) ->
    wf σ2 ->
    exists Σ', (Σ1 ≪ Σ') /\
            (Σ1 ≼ Σ') /\
            (Σ1 ▷ Σ') /\
            (Σ' ⊨ σ2) /\
            (Σ' ⊨ L2 : hot).
Proof.
  intros Σ1 Σ2 σ1 σ2 L1 L2 H1 H2.
  pose proof (storeSubset_finite _ _ H2).
  gen Σ1 Σ2 σ1 σ2 L1.
  eapply finite_sets_ind with (F := L2); eauto; intros.
  - exists Σ2; steps.
    intros l Hl. inversion Hl.
  - clear H L2. rename F into L2, a into l2.
    unfold Add in *.
    assert ((σ1, L1) ⋖ (σ2, L2)) by eauto with scp.
    pose proof (storeSubset_union_l _ _ _ H2).
    specialize (H1 Σ1 Σ2 σ1 σ2 H12 L1 H3 H H5 H6 H7 H8 H9 H10) as [Σ2' [ ]]; steps.
    clear Σ2 H5 H6 H7 H9.
    pose proof (synchronization Σ2' σ2 l2 H11 H15) as [Σ'' [ ]] ; steps.
    + assert (l' < dom σ1 \/ l' >= dom σ1) as [|] by lia.
      * specialize (H4 H3 H2 l' H6) as[l1 [H__l1 H__rch1]];[ exists l2; split; eauto with wf |].
        specialize (H10 l1 H__l1).
        lets: hot_transitivity  H10 H8 H__rch1.
        specialize (H14 l').
        meta; steps; meta; eauto with typ.
        exists C. eapply vt_sub; eauto with typ.
      * specialize (H1 l') as [ ]; eauto.
        -- assert (in_dom Σ2' l2) by admit.
        -- specialize (H8 l' H1); steps. apply getObj_dom in H8. lia.
    + exists Σ''; repeat split; eauto with typ.
      intros l0 [ l2' | ]; try inSingleton; eauto with rch wf typ.
Qed.
