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

  Definition storeSubset (σ: Store) L := (forall l, (l ∈ L) -> l < (dom σ)).
  Notation "L ⪽ σ" := (storeSubset σ L) (at level 80).

  Definition scoping (σ σ': Store) (L L': Ensemble Loc) :=
    L ⪽ σ ->
    L' ⪽ σ' ->
    (forall l, l < (dom σ) -> (σ' ⊫ L' ⇝ l) -> σ ⊫ L ⇝ l).
  Notation "a ⋖ b" := (scoping (fst a) (fst b) (snd a) (snd b)) (at level 81).

  Definition scoping_preservation (σ1 σ2: Store) (L: LocSet) :=
    (L ⪽ σ1) /\
    forall σ0 (L0 L1: Ensemble Loc),
      (dom σ0) <= (dom σ1) ->
      (dom σ0) <= (dom σ2) ->
      L0 ⪽ σ0 ->
      L1 ⪽ σ1 ->
      (σ0, L0) ⋖ (σ1, L) ->
      (σ0, L0) ⋖ (σ1, L1) ->
      (σ0, L0) ⋖ (σ2, L1).

  Notation "σ1 ⇝ σ2 ⋖ L" := (scoping_preservation σ1 σ2 L) (at level 81, σ2 at level 80, L at level 80).

  (* Results : *)


  Lemma scoping_reflexivity : forall (σ: Store) (L1 L2: Ensemble Loc), (L2 ⊆ L1) -> ((σ, L1) ⋖ (σ, L2)).
  Proof.
    intros.
    unfold scoping, reachability_set.
    simpl.
    intros A1 A2 l Hdom H1.
    move: H1 => [l' [Hl'1 Hl'2]].
    exists l'; split => //.
    unfold Included in H.
    auto.
  Qed.

  Lemma scoping_subset : forall σ1 σ2 L L1 L2, (σ1, L1)  ⋖ (σ2, L2∪L) ->
                                          L2∪L ⪽ σ2 ->
                                          (σ1, L1)  ⋖ (σ2, L).
  Proof.
    unfold scoping, reachability_set.
    simpl.
    intros.
    apply H => //.
    move: H4 => [l' [Hl'1 Hl'2]].
    exists l'; split => //.
    apply Union_intror.
    auto.
  Qed.

  Lemma scoping_union :  forall σ1 σ2 L L1 L2, (σ1, L)  ⋖ (σ2, L1) ->
                                          (σ1, L)  ⋖ (σ2, L2) ->
                                          (σ1, L)  ⋖ (σ2, L1∪L2).
  Proof.
    unfold scoping, reachability_set.
    simpl.
    intros.
    move: H4 => [l' [Hl'1 Hl'2]].
    move /(_ H1):H => H.
    move /(_ H1):H0 => H0.
    induction Hl'1 as [l' | l'].
    + apply H ; repeat exists l' ; auto => //.
      move => l'' Hl'' . apply (H2 l'').
      apply Union_introl => //.
    + apply H0 ; repeat exists l' ; auto => //.
      move => l'' Hl'' . apply (H2 l'').
      apply Union_intror => //.
  Qed.


  Lemma scoping_reachability: forall σ l1 l2, ( σ ⊨ l1 ⇝ l2) -> (σ, {l1}) ⋖ (σ, {l2}).
  Proof.
    unfold scoping, reachability_set ; simpl.
    intros.
    move: H3 => [l' [Hl'1 Hl'2]].
    induction Hl'1.
    exists l1 ; split; eauto using reachability_trans => //.
  Qed.

  Lemma scoping_transitivity: forall σ1 σ2 σ3 L1 L2 L3, (dom σ1) <= (dom σ2) ->
                                                   L2 ⪽ σ2 -> (* ADDED HYPOTHESIS *)
                                                   (σ1, L1) ⋖ (σ2, L2) ->
                                                   (σ2, L2) ⋖ (σ3, L3) ->
                                                   (σ1, L1) ⋖ (σ3, L3).
  Proof.
    intros.
    unfold scoping, reachability_set ; simpl.
    intros.
    move : H6 => [l3 [H_in_l3 H_reach_l3]].
    move: (PeanoNat.Nat.lt_le_trans l (dom σ1) _ H5 H) => B1.
    apply H1; simpl => //.
    apply H2; simpl => //.
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
    intros σ1 σ2 σ3 L1 [H_12_dom H_12] H_dom [H_23_dom H_23]. unfold scoping_preservation in *.
    apply (preserving_transitivity σ1 σ2 σ3 L1 L1) => //.
    apply (scoping_transitivity σ1 σ2 σ2 L1 L1 L1); steps.
    eapply H_12; steps; eauto.
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
      admit. (* Reasonning on graphs *)
  Admitted.

  Definition codom (ρ: Env) : (LocSet):=
    fun (l: Loc) => (List.In l ρ).

  Check forall (l : Loc), ~ (Singleton Loc l) = (Empty_set Loc).

  Ltac inSingleton :=
    match goal with
    |H: ?a ∈ Singleton Loc ?b |- _ => induction H
    end.

  Lemma scopability_theorem:
    forall e σ σ' ρ ψ l k,
      ⟦e⟧(σ, ρ, ψ)(k) = (Success l σ') ->
      ((σ, ((codom ρ) ∪ (Singleton Loc ψ))) ⋖ (σ', {l})) /\ (σ ⇝ σ' ⋖ ((codom ρ) ∪ (Singleton Loc ψ))) .
    move => e σ σ' ρ ψ l k.
    move: k e σ σ' ρ ψ l.
    apply (strong_induction (fun k => forall e σ σ' ρ ψ l, ⟦e⟧(σ, ρ, ψ)(k) = (Success l σ') ->
      ((σ, ((codom ρ) ∪ (Singleton Loc ψ))) ⋖ (σ', {l})) /\ (σ ⇝ σ' ⋖ ((codom ρ) ∪ (Singleton Loc ψ))))).
    intros n H_strong e σ σ' ρ ψ l H_success.
    destruct n; simpl; try discriminate.
    simpl in H_success; repeat destruct_match; try discriminate; try invert_constructor_equalities; subst.
    + (* e = x *)
      split.
      unfold scoping; steps.
      exists l; steps.
      apply Union_introl.
      unfold getVal in *.
      pose proof (nth_error_In ρ v matched0). unfold codom.
      unfold In => //. unfold reachability_set in *; steps. unfold In in H3. induction H3 => //.
      unfold scoping_preservation.
      steps.
      admit. (* Stuck on "(codom ρ ∪ {ψ}) ⪽ σ'" *)
    + (* e = this *)
      split. unfold scoping; steps.
      unfold reachability_set in *; steps. unfold In in H3. induction H3 => //.
      exists l. steps; eauto using Union_intror.
      unfold scoping_preservation.
      steps.
      admit. (* Stuck on "(codom ρ ∪ {ψ}) ⪽ σ'" *)
    + (* e = e0.f *)
      unfold scoping; intros.
      move /(_ n (le_n (S n)) ) : H_strong => H_strong.
      pose proof (PartialMonotonicity.partialMonotonicity_theorem_dom _ _ _ _ _ _ _ matched0).
      move : (H_strong _ _ _ _ _ _ matched0) => [A2 A3].
      assert ((σ', {v0}) ⋖ (σ', {l})) as B1. {
        apply scoping_reachability.
        eapply rch_trans; eauto.
        apply rch_heap; eauto using getObj_dom.

        admit. }
      assert ((σ,  (codom ρ) ∪ (Singleton Loc ψ)) ⋖ (σ', {l})) as C1.
      apply (scoping_transitivity _ σ' _ _ {v0}) => //.
      unfold storeSubset. intros. inSingleton. by apply (getObj_dom _ _ _ matched1).
      split. intros.
        by apply C1.
          by apply A3.
          Admitted.











End Scopability.
