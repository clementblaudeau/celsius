From Celsius Require Export Trees.
From Celsius Require Export Eval.
From Celsius Require Export PartialMonotonicity.
From Celsius Require Export Reachability.
From Celsius Require Export Compatibility.
From Celsius Require Export Wellformedness.
Require Import ssreflect ssrbool.
Require Import Psatz.

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
  Import Wellformedness.Wellformedness.

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

  Ltac inSingleton :=
    match goal with
    |H: ?a ∈ Singleton Loc ?b |- _ => induction H
    end.


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
      move => σ0 L0 L H_dom1 H_dom2' H_subL H_subL0 A1 A2.
      assert (dom σ2 = dom σ2') as H_dom22'. rewrite /dom H4 update_one3 => //.
      move :(H_dom2') => H_dom2. rewrite -H_dom22' in H_dom2.
      assert ((σ0, L0) ⋖ (σ2, L)) as B1 by (apply H; eauto).
      assert ((σ0, L0) ⋖ (σ2, {l'})) as C1. {
        eapply (scoping_transitivity _ σ1 _ L0 L1 {l'} ); eauto.
        apply H.
      }
      unfold scoping; simpl.
      intros. move: H8 => [l2 [Hl2 D1]].
      destruct (PeanoNat.Nat.eq_dec l l'); subst.
      (* if l = l', the assignment is weakening *)
      ++ apply B1; simpl; eauto.
         intros l3 Hl3; unfold dom in *; erewrite <- update_one3; steps; eauto.
         exists l2; split; eauto. eapply reachability_weaken_assignment; eauto.
      ++ move: (proj2 (iff_and (reachable_path_reachability _ l2 l0)) D1) => [[D2 D3] | [p D2]].
         +++ rewrite <- D2 in *. apply B1; simpl; eauto.
             intros l3 Hl3. unfold dom in *. erewrite <- update_one3; steps; eauto.
             eexists; split; eauto; try apply rch_heap. unfold dom in *. erewrite <- update_one3; steps; eauto.
         +++ destruct (reachable_path_assignment σ2 _ C ω _ _ f l l' H2 eq_refl eq_refl D2) as [Hedge | Hpath].
             ++++ pose proof (contains_edge_last_edge _ _ _ Hedge) as [p2 [p3 [H9 H10]]].
                  rewrite H9 in D2.
                  assert (σ2 ⊨ l' ⇝ l0). {
                    apply reachable_path_reachability.
                    destruct (PeanoNat.Nat.eq_dec l' l0); [left; split; lia | right].
                    Opaque reachable_path.
                    destruct p2; steps.
                    exists p2. eapply contains_edge_assignment with (l' := l'); eauto.
                    + clear D2 Hedge. intros [p21 [p22 Hedge]]; steps.
                      destruct p22; steps.
                      apply H10. clear H10. unfold contains_edge.
                      destruct p21.
                      ++ exfalso. apply n. symmetry.
                         eapply (app_inj_tail p2 (p22++[l'])).
                         rewrite app_assoc_reverse; steps.
                      ++ pose proof (app_exists_last p21 l1); steps.
                         exists p', (l0::p22); steps.
                         apply (app_inv_tail [l']).
                         simpl. rewrite H4. rewrite H5.
                         rewrite H5 in H4.
                         repeat rewrite app_comm_cons in H4. rewrite app_assoc in H4.
                         apply app_inj_tail in H4; steps.
                         repeat rewrite <- app_comm_cons || rewrite app_assoc_reverse.
                         steps.
                    + eapply (reachable_path_app2 _ l'(l::p3) (l1::p2)).
                      rewrite <- app_comm_cons; eauto.
                  }
                  apply C1; simpl; eauto.
                  apply_anywhere reachability_dom.
                  unfold storeSubset; intros; inSingleton; steps.
                  exists l'; split; eauto using In_singleton.
             ++++ apply B1; simpl; eauto.
                  intros l3 Hl3. unfold dom in *. erewrite <- update_one3; steps; eauto.
                  exists l2 ; split => // .
                  apply reachable_path_reachability; right; eauto.
    + (* (σ1, L1) ⋖ (σ2', {l}) *)
      unfold scoping; simpl. intros H5 H6 l1.
      steps. destruct H8; steps; inSingleton.
      destruct (PeanoNat.Nat.eq_dec l l'); subst.
      ++ (* if l = l', the assignment is weakening *)
        apply H0; unfold storeSubset in *; steps;
          try inSingleton; repeat rewrite_anywhere update_dom; eauto using In_singleton.
         eexists; split; eauto using In_singleton, reachability_weaken_assignment.
      ++ move: (proj2 (iff_and (reachable_path_reachability _ l l1)) H8) => [[D1 D2] | [p D1]]; subst.
      +++ assert (σ2 ⊨ l1 ⇝ l1) by eauto using rch_heap, getObj_dom.
         apply H0; unfold storeSubset; steps; try inSingleton; rewrite_anywhere update_dom; eauto.
         eexists; split; eauto using In_singleton.
      +++ destruct (reachable_path_assignment σ2 _ C ω _ _ f l l' H2 eq_refl eq_refl D1) as [Hedge | Hpath].
          ++++ (* path contains the edge *)
            assert (l' < dom σ2). {
              unfold contains_edge in Hedge. steps.
              eapply reachable_path_is_reachable in D1.
              eapply reachability_dom in D1. rewrite_anywhere update_dom; steps; eauto.
              rewrite H3. apply in_app_iff; steps.
            }
            apply H1; eauto.
            +++++ intros l3 Hl3. inSingleton => //.
            +++++ exists l'. steps.
            pose proof (contains_edge_last_edge _ _ _ Hedge) as [p2 [p3 [H9 H10]]].
            apply reachable_path_reachability.
            destruct (PeanoNat.Nat.eq_dec l' l1); [left; split; eauto | right].
            Opaque reachable_path.
            destruct p2; steps.
            exists p2.
            eapply contains_edge_assignment with (l' := l'); eauto.
            { clear D1 Hedge. intros [p21 [p22 Hedge]]; steps.
              destruct p22; steps.
              apply H10. clear H10. unfold contains_edge.
              destruct p21.
              ++ exfalso. apply n. symmetry.
                 eapply (app_inj_tail p2 (p22++[l'])).
                 rewrite app_assoc_reverse; steps.
              ++ pose proof (app_exists_last p21 l0); steps.
                 exists p', (l1::p22); steps.
                 apply (app_inv_tail [l']).
                 simpl. rewrite H9. rewrite H10.
                 rewrite H10 in H9.
                 repeat rewrite app_comm_cons in H9. rewrite app_assoc in H9.
                 apply app_inj_tail in H9; steps.
                 repeat rewrite <- app_comm_cons || rewrite app_assoc_reverse.
                 steps.
            } {
              eapply (reachable_path_app2 _ l'(l::p3) (l0::p2)).
              rewrite H4 in D1.
              rewrite <- app_comm_cons; eauto.
            }
          ++++ (* path does not contain the edge *)
            apply H0; simpl; eauto.
            +++++ intros l3 Hl3. inSingleton; eauto using reachability_dom, getObj_dom.
            +++++ exists l. steps.
                  apply reachable_path_reachability; right; eauto.
  Qed.


  Definition codom (ρ: Env) : (LocSet):=
    fun (l: Loc) => (List.In l ρ).


  Definition ScopabilityProp n :=
    forall e σ σ' ρ ψ l,
      ⟦e⟧(σ, ρ, ψ)(n) = (Success l σ') ->
      wf σ -> (codom ρ) ∪ {ψ} ⪽ σ ->
      ((σ, ((codom ρ) ∪ {ψ})) ⋖ (σ', {l})) /\ (σ ⇝ σ' ⋖ ((codom ρ) ∪ {ψ})) .

  Lemma scopability_theorem:
    forall n, ScopabilityProp n.
  Proof.
    apply strong_induction. unfold ScopabilityProp.
    intros n H_strong e σ σ' ρ ψ l H_success H_wf H_codom.
    destruct n => //.
    move /(_ n (le_n (S n)) ) : H_strong => H_strong.
    destruct e as [x | this | e0 f | e0 m el | C el | e0 f e1 e2]; simpl in H_success; repeat destruct_match; try discriminate; try invert_constructor_equalities; subst.
    + (* e = x *)
      split.
      unfold scoping; steps.
      exists l; steps.
      apply Union_introl.
      unfold codom, In. eauto using nth_error_In.
      apply_anywhere reachability_singleton => //.
      unfold scoping_preservation; steps.
    + (* e = this *)
      split. unfold scoping; steps.
      unfold reachability_set in *; steps. inSingleton.
      exists l. steps; eauto using Union_intror.
      unfold scoping_preservation; steps.
    + (* e = e0.f *)
      unfold scoping; intros; simpl.
      pose proof (PartialMonotonicity.partialMonotonicity_theorem_dom _ _ _ _ _ _ _ matched).
      move : (H_strong _ _ _ _ _ _ matched H_wf H_codom) => [A2 A3].
      assert ((σ', {v}) ⋖ (σ', {l})) as B1. {
        apply scoping_reachability.
        eapply rch_trans; eauto.
        apply rch_heap; eauto using getObj_dom.
        eapply wellformedness_conserved in matched0; eauto.
      }
      assert ((σ,  (codom ρ) ∪ (Singleton Loc ψ)) ⋖ (σ', {l})) as C1. {
      apply (scoping_transitivity _ σ' _ _ {v}) => //.
      unfold storeSubset. intros. inSingleton. eauto using getObj_dom.
      }
      steps.
    + (* e = e0.m(l0) *)
      rename matched into A1.
      rename s into σ0. rename l0 into lv. rename v into l0. rename e into ω.
      pose proof (H_strong _ _ _ _ _ _ A1 H_wf H_codom) as [A2 A3].
      assert ((σ, (codom ρ) ∪ {ψ}) ⋖ (σ0, (codom ρ) ∪ {ψ})) as A4
          by eauto using  preserving_regularity_degenerate, PartialMonotonicity.partialMonotonicity_theorem_dom.
      rename matched0 into A5. move: A1 A2 A3 A4 A5 => A1 A2 A3 A4 A5.
      rename s0 into σ_n. admit.
    + (* e = new C(l0) *)
      admit.
    + (* e = e0.f = e1; e2 *)
      rename matched into A0, s into σ0, v into l0, s0 into σ1, v0 into l1, matched0 into B0, H_success into E0.
      move: (PartialMonotonicity.partialMonotonicity_theorem_dom _ _ _ _ _ _ _ A0) => A_dom.
      move: (H_strong _ _ _ _ _ _ A0 H_wf H_codom) => [A1 A2].
      move: (preserving_regularity_degenerate _ _ _ A2 A_dom) => A3.
      move: (PartialMonotonicity.partialMonotonicity_theorem_dom _ _ _ _ _ _ _ B0) => B_dom.
      move: (wellformedness_conserved _ _ _ _ _ _ _ A0 H_wf H_codom) => [H_wf0 H_l0].
      assert ((codom ρ ∪ {ψ}) ⪽ σ0) as H_codom0 by eauto using storeSubset_trans.
      move: (H_strong _ _ _ _ _ _ B0 H_wf0 H_codom0) => [B1 B2].
      assert ((σ, codom ρ ∪ {ψ}) ⋖ (σ1, {l1})) as B3 by eauto using scoping_transitivity.
      assert ((σ, codom ρ ∪ {ψ}) ⋖ (σ1, {l0})) as B4 by (eapply B2; eauto; try lia; unfold storeSubset; intros; inSingleton; steps).
      unfold assign in E0.
      assert (dom σ0 <= dom σ1) by eauto with pM.
      repeat destruct_match; try solve [  eapply nth_error_None in matched; unfold dom in *; lia].

      set (σ1' :=  ([l0 ↦ (c, [f ↦ l1] (e))] (σ1))) in E0.
      assert (dom σ0 <= dom σ1') by (rewrite update_dom; lia).
      assert (dom σ <= dom σ1') by (rewrite update_dom; lia).
      assert (σ ⇝ σ1 ⋖ codom ρ ∪ {ψ}) as B5 by eauto using preserving_transitivity_degenerate.
      move: (scopability_assignment _ _ σ1' _ _ _ _ _ _ _ B5 B4 B3 matched eq_refl eq_refl) => [D2 D1].
      assert ((σ, codom ρ ∪ {ψ}) ⋖ (σ1', codom ρ ∪ {ψ})) as D3 by
            (eapply D2; try eapply scoping_reflexivity; steps; eauto using PeanoNat.Nat.le_trans with lia).
      assert ((codom ρ ∪ {ψ}) ⪽ σ1') as H_codom1' by eauto using storeSubset_trans.
      assert (wf σ1') as H_wf1'. {
        assert (wf σ1) by (eapply wellformedness_conserved; eauto).
        eapply wf_assign; eauto. steps.
        eapply wellformedness_conserved; eauto.
      }
      move: (H_strong _ _ _ _ _ _ E0 H_wf1' H_codom1') => [E1 E2].
      split; eauto using scoping_transitivity, preserving_transitivity.
  Admitted.


















End Scopability.
