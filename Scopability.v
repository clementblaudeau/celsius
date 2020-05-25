From Celsius Require Export Trees.
From Celsius Require Export Tactics.
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

  Definition storeSubset (σ: Store) L := (forall l, (l ∈ L) -> l < (dom σ)).
  Notation "L ⪽ σ" := (storeSubset σ L) (at level 80).

  Definition scoping (σ σ': Store) (L L': Ensemble Loc) :=
    L ⪽ σ /\
    L' ⪽ σ' /\
    (forall l, l < (dom σ) -> (σ' ⊫ L' ⇝ l) -> σ ⊫ L ⇝ l).
  Notation "a ⋖ b" := (scoping (fst a) (fst b) (snd a) (snd b)) (at level 81).

  Definition scoping_preservation (σ1 σ2: Store) (L: LocSet) :=
    forall σ0 (L0 L1: Ensemble Loc),
      L0 ⪽ σ0 ->
      L1 ⪽ σ1 ->
      (σ0, L0) ⋖ (σ1, L) ->
      (σ0, L0) ⋖ (σ1, L1) ->
      (σ0, L0) ⋖ (σ2, L1).

  Notation "σ1 ⇝ σ2 ⋖ L" := (scoping_preservation σ1 σ2 L) (at level 81, σ2 at level 80, L at level 80).

  (* Results : *)


  Lemma scoping_reflexivity : forall (σ: Store) (L1 L2: Ensemble Loc), (L2 ⊆ L1) -> (L1 ⪽ σ) -> ((σ, L1) ⋖ (σ, L2)).
  Proof.
    intros.
    unfold scoping, reachability_set.
    simpl. split => //.
    split;
    move => l Hl; eauto.
    move => [l' [A1 A2]].
    exists l'; split => //.
    auto.
  Qed.

  Hint Resolve Union_intror Union_introl:core.

  Lemma scoping_subset : forall σ1 σ2 L L1 L2, (σ1, L1)  ⋖ (σ2, L2∪L) ->
                                          (σ1, L1)  ⋖ (σ2, L).
  Proof.
    unfold scoping, reachability_set.
    simpl.
    move => σ1 σ2 L L1 L2 [HL1 [HLL2 A1]].
    split => //.
    split. move => l Hl ; auto.
    move => l Hdom [l' [B1 B2]].
    apply A1 => //.
    exists l'; split => //.
    auto.
  Qed.

  Lemma scoping_union :  forall σ1 σ2 L L1 L2, (σ1, L)  ⋖ (σ2, L1) ->
                                          (σ1, L)  ⋖ (σ2, L2) ->
                                          (σ1, L)  ⋖ (σ2, L1∪L2).
  Proof.
    unfold scoping, reachability_set.
    simpl.
    move => σ1 σ2 L L1 L2 [A1 [A2 A3]] [A4 [A5 A6]].
    split => //.
    split. move => l Hl;induction Hl; auto.
    move => l Hdom [l' [B1 B2]].
    induction B1 as [l' | l']; auto.
    + apply A3; repeat (auto ; exists l'; split).
    + apply A6; repeat (auto ; exists l'; split).
  Qed.

  Lemma scoping_reachability: forall σ l1 l2, ( σ ⊨ l1 ⇝ l2) -> (σ, {l1}) ⋖ (σ, {l2}).
  Proof.
    unfold scoping. simpl.
    intros.
    split. induction 1. apply (proj1 (reachability_dom _ _ _ H)).
    split. induction 1. apply (proj2 (reachability_dom _ _ _ H)).
    move => l Hdom A1.
    exists l1; split => //.
    move: A1 => [l' [B1 B2]].
    induction B1.
    apply (reachability_trans _ _ l2 _) => //.
  Qed.

  Lemma scoping_transitivity: forall σ1 σ2 σ3 L1 L2 L3, (dom σ1) <= (dom σ2) ->
                                                   (σ1, L1) ⋖ (σ2, L2) ->
                                                   (σ2, L2) ⋖ (σ3, L3) ->
                                                   (σ1, L1) ⋖ (σ3, L3).
  Proof.
    move => σ1 σ2 σ3 L1 L2 L3 H_dom H1 H2.
    unfold scoping, reachability_set ; simpl.
    split. apply (proj1 H1).
    split. apply (proj1 (proj2 H2)).
    move => l Adom [l3 [A1 A2]].
    move: (PeanoNat.Nat.lt_le_trans l (dom σ1) _ Adom H_dom) => B1.
    apply (proj2 (proj2 H1)); simpl => //.
    apply (proj2 (proj2 H2)); simpl => //.
    exists l3 => //.
  Qed.

  Lemma preserving_transitivity: forall σ1 σ2 σ3 L1 L2, (σ1 ⇝ σ2 ⋖ L1) ->
                                                   (σ2 ⇝ σ3 ⋖ L2) ->
                                                   (σ1, L1) ⋖ (σ2, L2) ->
                                                   (dom σ1) <= (dom σ2) ->  (* ADDED HYPOTHESIS *)
                                                   (σ1 ⇝ σ3 ⋖ L1).
  Proof.
    intros.
    unfold scoping_preservation.
    split.
    + apply (proj1 H).
    + move => σ0 L0 L H_dom1 H_dom3 H_subL0 H_subL A1 A2.
    move: (PeanoNat.Nat.le_trans _ _ _ H_dom1 H2) => H_dom2.
    move : ((proj2 H) _ _ _  H_dom1 H_dom2 H_subL0 H_subL A1 A2) => B1.
    move: (scoping_transitivity σ0 σ1 σ2 L0 L1 L2 H_dom1 (proj1 H) A1 H1) => C1.
    apply (proj2 H0) => //.
    move => l Hl.
    apply (PeanoNat.Nat.lt_le_trans _ (dom σ1) _) => //.
    apply (H_subL _ Hl).
  Qed.


  Lemma preserving_regularity_degenerate: forall σ1 σ2 L, σ1 ⇝ σ2 ⋖ L -> (dom σ1) <= (dom σ2) -> (σ1, L) ⋖ (σ2, L).
  Proof.
    intros.
    move: H => [H_subL H_pres].
    move: (PeanoNat.Nat.le_refl (dom σ1)) => H_dom1.
    assert (L ⊆ L) as Hincluded. move => x => //.
    move: (scoping_reflexivity σ1 L L Hincluded) => Href.
    apply (H_pres  σ1 L L H_dom1 H0 H_subL H_subL Href Href).
    Qed.

  Lemma preserving_regularity: forall σ0 σ1 σ2 L L1, σ1 ⇝ σ2 ⋖ L ->
                                                (dom σ0) <= (dom σ2) -> (* ADDED HYPOTHESIS *)
                                                (dom σ0) <= (dom σ1) -> (* ADDED HYPOTHESIS *)
                                                L ⪽ σ0 -> (* ADDED HYPOTHESIS *)
                                                L1 ⪽ σ1 -> (* ADDED HYPOTHESIS *)
                                                (σ0, L) ⋖ (σ1, L) ->
                                                (σ0, L) ⋖ (σ1, L1) ->
                                                (σ0, L) ⋖ (σ2, L1).
  Proof.
    intros.
    apply (proj2 H) => //.
  Qed.

  Lemma preserving_transitivity_degenerate: forall σ1 σ2 σ3 L1 , σ1 ⇝ σ2 ⋖ L1 ->
                                                (dom σ1) <= (dom σ2) -> (* ADDED HYPOTHESIS *)
                                                 σ2 ⇝ σ3 ⋖ L1 ->
                                                 σ1 ⇝ σ3 ⋖ L1.
  Proof.
    intros.
    apply (preserving_transitivity σ1 σ2 σ3 L1 L1) => //.
    apply (scoping_transitivity σ1 σ2 σ2 L1 L1 L1) => //.
    apply (proj1 H1).
    apply (proj2 H) => //.
    apply (proj1 H).
    apply (proj1 H).
  Qed.

  Lemma scopability_assignment: forall σ1 σ2 σ2' L1 l l' f C ω ω',
      σ1 ⇝ σ2 ⋖ L1 ->
      (σ1, L1) ⋖ (σ2, {l}) ->
      (σ1, L1) ⋖ (σ2, {l'}) ->
      (getObj σ2 l) = Some (C, ω) ->
      ω' = [f ↦ l']ω ->
      σ2' = [l ↦ (C, ω')]σ2 ->
      (σ1 ⇝ σ2' ⋖ L1) /\ ((σ1, L1) ⋖ (σ2', {l})).
    intros.
    split.
    + (* σ1 ⇝ σ2' ⋖ L1 *)
      split. apply (proj1 H).
      move => σ0 L L0 H_dom1 H_dom2' H_subL H_subL0 A1 A2.
      assert (dom σ2 = dom σ2') as H_dom22'. rewrite /dom H4 update_one3 => //.
      move :(H_dom2') => H_dom2. rewrite -H_dom22' in H_dom2.
      admit.
      Admitted.










End Scopability.
