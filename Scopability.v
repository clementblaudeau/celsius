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

(*
  Notation "σ ⊨ l1 ⇝ l2" := (σ + l1 + l2) (at level 80, l1 at level 80, l2 at level 80).
  Notation "σ1 ⇝ σ2 ⋖ L" := (σ1 * σ2 * L) (at level 81, σ2 at level 81).
  Eval compute in (2 ⊨ 2 ⇝ 3) + (1 ⇝ 2 ⋖ 3).
  Check (1 ⊨ 2 ⇝ 3).
  Check (2 ⇝ 3 ⋖ 4).
*)

Module Scopability.
  Import Eval.Evaluator.
  Import Reachability.Reachability.

  Definition scoping (σ1 σ2: Store) (L1 L2: Ensemble Loc) := forall l, l < (dom σ1) -> (σ2 ⊫ L2 ⇝ l) -> σ1 ⊫ L1 ⇝ l.
  Notation "a ⋖ b" := (scoping (fst b) (fst a) (snd b) (snd a)) (at level 81).

  Definition scoping_preservation (σ1 σ2: Store) L :=
    forall σ0 (L0 L1: Ensemble Loc),
      (forall l, (l ∈ L0) -> l < (dom σ0)) ->
      (forall l, (l ∈ L1) -> l < (dom σ1)) ->
      (σ1, L)  ⋖ (σ0, L0) ->
      (σ1, L1) ⋖ (σ0, L0) ->
      (σ2, L1) ⋖ (σ0, L0).

  Notation "σ1 ⇝ σ2 ⋖ L" := (scoping_preservation σ1 σ2 L) (at level 81, σ2 at level 80, L at level 80).

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

  Lemma scoping_subset : forall σ1 σ2 L L1 L2, (σ2, L2)  ⋖ (σ1, L1) ->
                                          L ⊆ L2 ->
                                          (σ2, L)  ⋖ (σ1, L1).
  Proof.
    unfold scoping, reachability_set.
    simpl.
    intros.
    apply (H l H1).
    move: H2 => [l' [Hl'1 Hl'2]].
    exists l'; split => //.
    unfold Included in H0.
    auto.
  Qed.

  Lemma scoping_union :  forall σ1 σ2 L L1 L2, (σ2, L1)  ⋖ (σ1, L) ->
                                          (σ2, L2)  ⋖ (σ1, L) ->
                                          (σ2, L1∪L2)  ⋖ (σ1, L).
  Proof.
    unfold scoping, reachability_set.
    simpl.
    intros.
    move: H2 => [l' [Hl'1 Hl'2]].
    induction Hl'1 as [l' | l']; repeat eauto ; exists l'.
  Qed.

  Locate "⊨".
  Lemma scoping_reachability: forall σ l1 l2, ( σ ⊨ l1 ⇝ l2) -> (σ, {l2}) ⋖ (σ, {l1}).
    Proof.
      unfold scoping, reachability_set ; simpl.
      intros.
      move: H1 => [l' [Hl'1 Hl'2]].
      induction Hl'1.
      exists l1 ; split => //.
      apply (reachability_trans σ l1 l2 l H Hl'2).
    Qed.

    Lemma scoping_transitivity: forall σ1 σ2 σ3 L1 L2 L3, (dom σ1) <= (dom σ2) ->
                                                     (σ2, L2) ⋖ (σ1, L1) ->
                                                     (σ3, L3) ⋖ (σ2, L2) ->
                                                     (σ3, L3) ⋖ (σ1, L1).
      Proof.
      unfold scoping, reachability_set ; simpl.
      intros.
      move: (PeanoNat.Nat.lt_le_trans l (dom σ1) _ H2 H) => H_dom.
      move /(_ l H_dom H3):H1 => H4.
      move /(_ l H2 H4):H0 => [l' [H5 H6]].
      exists l' => //.
      Qed.


  End Scopability.