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

  Lemma preserving_transitivity: forall σ1 σ2 σ3 L1 L2, (σ1 ⇝ σ2 ⋖ L1) ->
                                                   (σ2 ⇝ σ3 ⋖ L2) ->
                                                   (σ2, L2) ⋖ (σ1, L1) ->
                                                   (σ1 ⇝ σ3 ⋖ L1).
  Proof.
    intros.
    unfold scoping_preservation.
    intros σ0 L0 L HL0 HL A1 A2.
    move : (H _ _ _ HL0 HL A1 A2) => B1.
    assert (dom σ0 <= dom σ1). admit. (* dom σ0 ⊆ dom σ1 required by scoping transitivity *)
    move: (scoping_transitivity _ _ _ _ _ _ H2 A1 H1) => C1.
    assert ( forall l : Loc, l ∈ L -> l < dom σ2). admit. (* L ⊆ σ2 required by scoping preservation *)
    apply (H0 _ _ _ HL0 H3 C1 B1).
  Admitted.

  Lemma preserving_regularity_environment: forall σ1 σ2 L, σ1 ⇝ σ2 ⋖ L -> (σ2, L) ⋖ (σ1, L).
  Proof.
    intros.
    assert ( forall l : Loc, l ∈ L -> l < dom σ1). admit. (* L ⊆ σ1 required by scoping preservation *)
    assert (L ⊆ L) as Hincluded. move => x => //.
    move: (scoping_reflexivity σ1 L L Hincluded) => Href.
    apply (H σ1 L L H0 H0 Href Href).
  Admitted.

  Lemma preserving_regularity: forall σ0 σ1 σ2 L L1, σ1 ⇝ σ2 ⋖ L ->
                                                (σ1, L) ⋖ (σ0, L) ->
                                                (σ1, L1) ⋖ (σ0, L) ->
                                                (σ2, L1) ⋖ (σ0, L).
  Proof.
    intros.
    apply H => //.
    admit. (* L ⊆ σ0 *)
    admit. (* L1 ⊆ σ1 *)
  Admitted.

  Lemma preserving_transitivity_degenerate: forall σ1 σ2 σ3 L1 , σ1 ⇝ σ2 ⋖ L1 ->
                                                 σ2 ⇝ σ3 ⋖ L1 ->
                                                 σ1 ⇝ σ3 ⋖ L1.
  Proof.
    intros.
    move: (preserving_regularity_environment _ _ _ H) => A1.
    apply: (preserving_transitivity _ _ _ _ _ H H0 A1) => //.
  Qed.







End Scopability.
