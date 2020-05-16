From Celsius Require Export Trees.
From Celsius Require Export Eval.
From Celsius Require Export PartialMonotonicity.
From Celsius Require Export Reachability.
From Celsius Require Export Compatibility.
Require Import ssreflect ssrbool.

Require Import List.
Import ListNotations.
Open Scope nat_scope.
Require Import Sets.Ensembles.


Module Scopability.
  Import Eval.Evaluator.
  Import Reachability.Reachability.

  Definition scoping (σ1 σ2: Store) (L1 L2: Ensemble Loc) := forall l, l < (dom σ1) -> (σ2 ⊫ L2 ⇝ l) -> σ1 ⊫ L1 ⇝ l.
  Notation "a ⋖ b" := (scoping (fst b) (fst a) (snd b) (snd a)) (at level 80).

  Definition scoping_preservation (σ1 σ2: Store) L :=
    forall σ0 (L0 L1: Ensemble Loc),
      (forall l, (l ∈ L0) -> l < (dom σ0)) ->
      (forall l, (l ∈ L1) -> l < (dom σ1)) ->
      (σ1, L)  ⋖ (σ0, L0) ->
      (σ1, L1) ⋖ (σ0, L0) ->
      (σ2, L1) ⋖ (σ0, L0).

  Notation "σ1 ⇝ σ2 ⋖ L" := (scoping_preservation σ1 σ2 L) (at level 80, L at level 99, σ2 at level 99).

  (* Results : *)

  Lemma scoping_reflexivity : forall (σ: Store) (L1 L2: Ensemble Loc), (Included Loc L1 L2) -> ((σ, L1) ⋖ (σ, L2)).
  Proof.
    unfold scoping, reachability_set.
    simpl.
    intros.
    move: H1 => [l' [Hl'1 Hl'2]].
    exists l'; split => //.
    unfold Included in H.
    auto.
  Qed.
