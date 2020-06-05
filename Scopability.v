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
  Create HintDb scop.


  Definition storeSubset (σ: Store) L := (forall l, (l ∈ L) -> l < (dom σ)).
  Notation "L ⪽ σ" := (storeSubset σ L) (at level 80).

  Definition scoping (σ σ': Store) (L L': Ensemble Loc) :=
    (forall l, l < (dom σ) -> (σ' ⊫ L' ⇝ l) -> σ ⊫ L ⇝ l) /\ (dom σ) <= (dom σ').
  Notation "a ⋖ b" := (scoping (fst a) (fst b) (snd a) (snd b)) (at level 81).

  Definition scoping_preservation (σ1 σ2: Store) (L: LocSet) :=
    forall σ0 (L0 L1: Ensemble Loc),
      (σ0, L0) ⋖ (σ1, L) ->
      (σ0, L0) ⋖ (σ1, L1) ->
      (σ0, L0) ⋖ (σ2, L1).

  Notation "σ1 ⇝ σ2 ⋖ L" := (scoping_preservation σ1 σ2 L) (at level 81, σ2 at level 80, L at level 80).
  Hint Unfold scoping_preservation: scop.

  (* Results : *)

  Lemma scoping_reflexivity : forall (σ: Store) (L1 L2: Ensemble Loc), (L2 ⊆ L1) -> (L1 ⪽ σ) -> ((σ, L1) ⋖ (σ, L2)).
  Proof.
    intros.
    unfold scoping, reachability_set; simpl.
    split => //.
    move => l Hl [l' [A1 A2]].
    exists l'; split => //.
    auto.
  Qed.

  Hint Resolve Union_intror Union_introl:core.

  Lemma scoping_subset : forall σ1 σ2 L L1 L2, (σ1, L1)  ⋖ (σ2, L2∪L) ->
                                          (σ1, L1)  ⋖ (σ2, L).
  Proof.
    unfold scoping, reachability_set.
    simpl.
    move => σ1 σ2 L L1 L2 [A1 A2].
    split => //.
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
    move => σ1 σ2 L L1 L2 A1 A2.
    split.
    move => l Hdom [l' [B1 B2]].
    induction B1 as [l' | l']; auto.
    + apply A1; repeat (auto ; exists l'; split).
    + apply A2; repeat (auto ; exists l'; split).
    + apply (proj2 A2).
  Qed.

  Lemma scoping_reachability: forall σ l1 l2, ( σ ⊨ l1 ⇝ l2) -> (σ, ⦃l1⦄) ⋖ (σ, ⦃l2⦄).
  Proof.
    unfold scoping. simpl.
    intros.
    split => //.
    exists l1; split => //.
    move: H1 => [l' [B1 B2]].
    induction B1.
    apply (reachability_trans _ _ l2 _) => //.
  Qed.

  Lemma scoping_transitivity: forall σ1 σ2 σ3 L1 L2 L3, (σ1, L1) ⋖ (σ2, L2) ->
                                                   (σ2, L2) ⋖ (σ3, L3) ->
                                                   (σ1, L1) ⋖ (σ3, L3).
  Proof.
    move => σ1 σ2 σ3 L1 L2 L3 H1 H2.
    unfold scoping, reachability_set ; simpl.
    split.
    + move => l Adom [l3 [A1 A2]].
    move: (PeanoNat.Nat.lt_le_trans l (dom σ1) _ Adom (proj2 H1)) => B1.
    apply H1; simpl => //.
    apply H2; simpl => //.
    exists l3 => //.
    + apply (PeanoNat.Nat.le_trans _ (dom σ2) _ (proj2 H1) (proj2 H2)) => //.
  Qed.

  Lemma preserving_transitivity: forall σ1 σ2 σ3 L1 L2, (σ1 ⇝ σ2 ⋖ L1) ->
                                                   (σ2 ⇝ σ3 ⋖ L2) ->
                                                   (σ1, L1) ⋖ (σ2, L2) ->
                                                   (σ1 ⇝ σ3 ⋖ L1).
  Proof.
    intros.
    unfold scoping_preservation.
    move => σ0 L0 L A1 A2 .
    unfold scoping. simpl.
    split.
    +  move => l Hl A0.
    assert ((σ0, L0) ⋖ (σ2, L)) as B1. {
      apply H => //. }
    assert ((σ0, L0) ⋖ (σ2, L2)) as C1. {
      apply (scoping_transitivity _ σ1 _ _ L1 _) => //. }
    unfold scoping_preservation in H0.
    move /(_ σ0 L0 L C1 B1):H0 => H0.
    apply ((proj1 H0) l Hl A0).
    + unfold scoping_preservation in H0.
      move /(_ σ0 L0 L (scoping_transitivity _ _ _ _ _ _ A1 H1)):H0 => H0.
      apply H0.
      apply H => //.
  Qed.


  Lemma preserving_regularity_degenerate: forall σ1 σ2 L, σ1 ⇝ σ2 ⋖ L ->
                                                     (σ1, L) ⋖ (σ2, L).
  Proof.
    intros.
    assert ((σ1, L) ⋖ (σ1, L)) as A1. {
      simpl => //. }
    apply H => //.
    Qed.

  Lemma preserving_regularity: forall σ0 σ1 σ2 L L1, σ1 ⇝ σ2 ⋖ L ->
                                                (σ0, L) ⋖ (σ1, L) ->
                                                (σ0, L) ⋖ (σ1, L1) ->
                                                (σ0, L) ⋖ (σ2, L1).
  Proof.
    intros.
    apply H => //.
  Qed.

  Lemma preserving_transitivity_degenerate: forall σ1 σ2 σ3 L1 , σ1 ⇝ σ2 ⋖ L1 ->
                                                 σ2 ⇝ σ3 ⋖ L1 ->
                                                 σ1 ⇝ σ3 ⋖ L1.
  Proof.
    intros.
    apply (preserving_transitivity σ1 σ2 σ3 L1 L1) => //.
    apply: (preserving_regularity_degenerate σ1 σ2 L1) => //.
  Qed.

  Lemma scopability_assignment: forall σ1 σ2 σ2' L1 l l' f C ω ω',
      σ1 ⇝ σ2 ⋖ L1 ->
      (σ1, L1) ⋖ (σ2, ⦃l⦄) ->
      (σ1, L1) ⋖ (σ2, ⦃l'⦄) ->
      (getObj σ2 l) = Some (C, ω) ->
      ω' = [f ↦ l']ω ->
      σ2' = [l ↦ (C, ω')]σ2 ->
      (σ1 ⇝ σ2' ⋖ L1) /\ ((σ1, L1) ⋖ (σ2', ⦃l⦄)).
  Proof.
    intros.
    split.
    + (*  σ1 ⇝ σ2' ⋖ L1 *)
      move => σ0 L0 L A1 A2.
      assert ( (σ0, L0) ⋖ (σ2, L)) as B1. {
        apply H => //. }
      assert ((σ0, L0) ⋖ (σ2, ⦃l'⦄)) as C1. {
        apply (scoping_transitivity _ _ _ _ _ _ A1 H1). }
      split; simpl.
      move => l2 Hl2.
      unfold reachability_set.
      move => [l0 [D0 D1]].
      admit. (* reasonning about paths *)
      rewrite /dom H4 update_one3.
      apply (proj2 B1).
    + split. simpl.
      move => l1 Hl1.
      rewrite {1}/reachability_set.
      move => [l'' [Hl'' A1]].
      induction Hl''.
      admit. (* reasonning about paths *)
      simpl.
      rewrite /dom H4 update_one3.
      apply (proj2 H0).
  Admitted.



  Fixpoint codom ρ : LocSet := match ρ with
                     | [] => (Empty_set Loc)
                     | v::ρ' => ⦃v⦄ ∪ (codom ρ') end.
  Lemma In_codom: forall ρ l v, (getVal ρ l = Some v) -> v ∈ (codom ρ).
  Proof.
    intros.
    generalize dependent l.
    induction ρ.
    + destruct l => //.
    + destruct l => //.
      simpl => H1.
      injection H1 => H2.
      apply Union_introl.
      rewrite H2 => //.
      simpl => H3.
      eauto using Union_intror.
      Qed.


  Definition scopability_prop (k : nat) :=  forall (e: Expr) (σ σ': Store) (ρ: Env) (ψ l: Value),
      ⟦e⟧(σ, ρ, ψ)(k) = (Success l σ') ->
      ((σ, (codom ρ) ∪ ⦃ψ⦄) ⋖ (σ', ⦃l⦄)) /\
      (σ ⇝ σ' ⋖ ((codom ρ) ∪ ⦃ψ⦄)).

  Lemma memoryGrowth: forall (k: nat) (e: Expr) (σ σ': Store) (ρ: Env) (ψ l: Value),
      ⟦e⟧(σ, ρ, ψ)(k) = (Success l σ') -> (dom σ) <= (dom σ').
  Proof.
    intros.
    apply PartialMonotonicity.partialMonotonicity_domains.
    apply (PartialMonotonicity.partialMonotonicity_theorem k e _ _ _ _ _ H).
  Qed.

  Hint Resolve memoryGrowth: scop.

  Lemma partialMonotonicity_theorem_rec_step : forall (n : nat),
      (* Strong induction *)
      (forall (k : nat), (k < n ) -> scopability_prop k) ->
      (scopability_prop n).

    (* To get one step of the evaluator, we destruct n *)
    destruct n.
    (* n = 0 - Timeout *)
    unfold scopability_prop => //.
    (* n > 0 - case analysis over e *)
    unfold scopability_prop.
    intros H_strong; intros.
    move : (PeanoNat.Nat.lt_succ_diag_r n) => Hn.
    destruct e; simpl in H.
    - (* case e = x *)
      destruct (getVal ρ v) eqn: Hval => //.
      invert_constructor_equalities.
      rewrite -H2.
      unfold scoping. split. repeat eauto || simpl || split.
      intros.
      move:H0 => [l' [H3 H4]].
      induction H3.
      exists l.
      split ; eauto .
      apply Union_introl.
      apply (In_codom _ v _) ; eauto.
      rewrite -H1 => //.
      unfold scoping_preservation. eauto.
    - (* case e = this *)
      invert_constructor_equalities. split.
      + (* 1 *) repeat eauto using memoryGrowth with scop || simpl || split || intros.
        exists l. split; eauto using Union_intror, In_singleton with scop.
        move: H0 => [l' [ H3 H4]].
        induction H3 => //.
      + unfold scoping_preservation. eauto.
    - (* case e = e0.f *)
      destruct (⟦ e ⟧ (σ, ρ, ψ )( n)) as [| | l0 σ1 | ] eqn: A1; try solve [congruence].
      destruct (getObj σ1 l0) as [[C ω] |] eqn: A4 => //.
      destruct (getVal ω v) eqn: A5 => //.
      invert_constructor_equalities.
      rewrite ?H1 ?H2 in A1, A4 A5.
      move: (H_strong n Hn _ _ _ _ _ _ A1) => [A2 A3].
      assert ((σ', ⦃l0⦄) ⋖ (σ', ⦃l⦄)) as C1. {
        apply scoping_reachability.
        move: (getObj_dom _ _ _ A4) => Hl0.
        apply: (rch_trans l0 l0 l C ω σ') => //.
        apply rch_heap => //.
        exists v => //.
        admit.
      }
      split => //.
      apply (scoping_transitivity _ σ' _ _ ⦃l0⦄ _) => //.

  Qed.










End Scopability.
