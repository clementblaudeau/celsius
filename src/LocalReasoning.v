(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines the main result of local reasoning, built upon wellformedness, compatibility, scopability and stackability. In a wellformed, fully initialized context, a newly created object can only access hot (transitively fully initialized) locations. *)

From Celsius Require Export Scopability Compatibility PartialMonotonicity Stackability.
Require Import ssreflect ssrbool Psatz Sets.Ensembles List.
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
