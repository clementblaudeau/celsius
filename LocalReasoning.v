(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines the main result of local reasoning, built upon wellformedness, compatibility, scopability and stackability. In a wellformed, fully initialized context, a newly created object can only access hot (transitively fully initialized) locations. *)

From Celsius Require Export Trees Eval PartialMonotonicity Reachability Compatibility Scopability Stackability Wellformedness.
Require Import ssreflect ssrbool Psatz Sets.Ensembles List.
Import ListNotations.
Open Scope nat_scope.

(** ** Local Reasoning theorem *)
(** We start with a lemma : *)
Lemma local_reasoning:
  forall σ σ' L L',
    L ⪽ σ ->
    L' ⪽ σ' ->
    (σ, L) ⋖ (σ', L') ->
    σ ≪ σ' ->
    σ ⊆ σ' ->
    σ ⪯ σ' ->
    (σ ⊫ L : hot) ->
    σ' ⊫ L' : hot.
Proof.
  intros; intros l' Hl'.
  assert (dom σ <= dom σ') by eauto with pM.
  destruct (PeanoNat.Nat.lt_ge_cases l' (dom σ)).
  + (* l ∈ (dom σ) *)
    eapply partialMonotonicity_warm_monotone; eauto .
    assert (reachability_set σ L l') by (eapply H1; simpl => //; eexists; eauto).
    inversion H9; steps.
    eapply H5; eauto with rch.
  + (* l ∉ (dom σ) *)
    eapply reachability_dom, H2 in Hl'; intuition.
Qed.

(* Then the main theorem : *)
Theorem Local_reasoning:
  forall e σ σ' ρ ψ l k,
    ⟦e⟧(σ, ρ, ψ)(k) = (Success l σ') ->
    wf σ ->
    (codom ρ ∪ {ψ}) ⪽ σ ->
    (σ ⊫ ((codom ρ) ∪ {ψ}) : hot) ->
    σ' ⊨ l : hot.
Proof.
  intros.
  assert (σ' ⊫ (Singleton Loc l) : hot). {
    eapply local_reasoning;
      eauto using stackability_theorem with pM stk cmpt wf lia.
    eapply scopability_theorem in H; eauto with pM wf lia; steps. }
  eapply H3; eauto using In_singleton.
Qed.
