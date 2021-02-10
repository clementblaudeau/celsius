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
  Create HintDb scoping.

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

  Lemma scoping_reflexivity2 : forall σ L, (σ, L) ⋖ (σ, L).
  Proof.
    intros.
    eapply scoping_reflexivity; steps.
  Qed.

  Hint Resolve scoping_reflexivity: scoping.
  Hint Resolve scoping_reflexivity2: scoping.

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
  Hint Resolve scoping_subset: scoping.

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

  Hint Resolve scoping_union: scoping.

  Lemma scoping_union_introl :
    forall σ1 σ2 L L1 L2,
      (L1 ∪ L2) ⪽ σ2 ->
      (σ1, L)  ⋖ (σ2, L1∪L2) ->
      (σ1, L)  ⋖ (σ2, L1).
  Proof.
    unfold scoping, reachability_set; simpl; steps.
    eapply_any; eauto.
    eexists; eauto using Union_introl.
  Qed.

  Hint Resolve scoping_union_introl: scoping.

  Lemma scoping_union_intror :
    forall σ1 σ2 L L1 L2,
      (L1 ∪ L2) ⪽ σ2 ->
      (σ1, L)  ⋖ (σ2, L1∪L2) ->
      (σ1, L)  ⋖ (σ2, L2).
  Proof.
    unfold scoping, reachability_set; simpl; steps.
    eapply_any; eauto.
    eexists; eauto using Union_intror.
  Qed.

  Hint Resolve scoping_union_intror: scoping.


  Lemma scoping_reachability: forall σ l1 l2, ( σ ⊨ l1 ⇝ l2) -> (σ, {l1}) ⋖ (σ, {l2}).
  Proof.
    unfold scoping, reachability_set ; simpl.
    intros.
    move: H3 => [l' [Hl'1 Hl'2]].
    induction Hl'1.
    exists l1 ; split; eauto using reachability_trans => //.
  Qed.
  Hint Resolve scoping_reachability: scoping.


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
  Hint Resolve scoping_transitivity: scoping.

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
  Hint Resolve preserving_transitivity: scoping.


  Lemma preserving_regularity_degenerate: forall σ1 σ2 L, σ1 ⇝ σ2 ⋖ L -> (dom σ1) <= (dom σ2) -> (σ1, L) ⋖ (σ2, L).
  Proof.
    intros.
    move: H => [H_subL H_pres].
    move: (PeanoNat.Nat.le_refl (dom σ1)) => H_dom1.
    assert (L ⊆ L) as Hincluded. move => x => //.
    move: (scoping_reflexivity σ1 L L Hincluded) => Href.
    apply (H_pres  σ1 L L H_dom1 H0 H_subL H_subL Href Href).
    Qed.
  Hint Resolve preserving_regularity_degenerate: scoping.

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
  Hint Resolve preserving_regularity: scoping.

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
  Hint Resolve preserving_transitivity_degenerate: scoping.

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

  Lemma scopability_add:
    forall σ σ' ρ' l0 l a,
      (σ, a) ⋖ (σ', {l}) ->
      (σ, a) ⋖ (σ', codom ρ' ∪ {l0}) ->
      (σ, a) ⋖ (σ', codom (l::ρ') ∪ {l0}).
  Proof.
    intros.
    assert ((codom (l :: ρ') ∪ {l0}) = Union Loc (Singleton Loc l) ( codom ρ' ∪ {l0})). {
      apply Extensionality_Ensembles.
      unfold Same_set; steps; intros l'; steps.
      + inversion H1. steps.
        apply Union_intror, Union_introl; steps.
        inSingleton; subst.
        apply Union_intror, Union_intror; steps.
      + inversion H1. inSingleton; subst.
        apply Union_introl; steps.
        inversion H2. steps.
        apply Union_introl; steps.
        steps. inSingleton.
        apply Union_intror; steps.
    }
    rewrite H1.
    apply scoping_union; eauto.
  Qed.


  Definition ScopabilityProp n :=
    forall e σ σ' ρ ψ l,
      ⟦e⟧(σ, ρ, ψ)(n) = (Success l σ') ->
      wf σ -> (codom ρ) ∪ {ψ} ⪽ σ ->
      ((σ, ((codom ρ) ∪ {ψ})) ⋖ (σ', {l})) /\ (σ ⇝ σ' ⋖ ((codom ρ) ∪ {ψ})) .

  Lemma scopability_list_aux:
    forall n,
      (forall k,
          k < S n ->
          forall (e : Expr) (σ σ' : Store) (ρ : Env) (ψ l : Value),
            (⟦ e ⟧ (σ, ρ, ψ )( k)) = Success l σ' ->
            wf σ -> (codom ρ ∪ {ψ}) ⪽ σ -> ((σ, codom ρ ∪ {ψ}) ⋖ (σ', {l})) /\ (σ ⇝ σ' ⋖ codom ρ ∪ {ψ})) ->
      forall e0 el σ ρ ψ l0 σ0 ρ' σ_n ,
        (⟦_ el _⟧ (σ0, ρ, ψ )(n)) = Success_list ρ' σ_n ->
        wf σ ->
        (codom ρ ∪ {ψ}) ⪽ σ ->
        (⟦ e0 ⟧ (σ, ρ, ψ )(n)) = Success l0 σ0 ->
        ((σ, codom ρ ∪ {ψ}) ⋖ (σ_n, codom ρ' ∪ {l0})) /\ (σ ⇝ σ_n ⋖ codom ρ ∪ {ψ}).
  Proof.
    intros.
    destruct n; try discriminate.
    simpl in H0.
    pose proof (H (S n) (le_n (S (S n))) _ _ _ _ _ _ H3 H1 H2) as [H_scope H_preserv].
    assert (forall el ρ' σ1 σ2 acc,
               fold_left (eval_list_aux ρ ψ n) el (Success_list acc σ1) = Success_list ρ' σ2 ->
               wf σ1 ->
               dom σ <= dom σ1 ->
               σ ⇝ σ1 ⋖ (codom ρ ∪ {ψ}) ->
               (codom acc ∪ {l0}) ⪽ σ1 ->
               ((σ, codom ρ ∪ {ψ}) ⋖ (σ1, codom acc ∪ {l0})) ->
               ((σ, codom ρ ∪ {ψ}) ⋖ (σ2, codom ρ' ∪ {l0})) /\ (σ ⇝ σ2 ⋖ codom ρ ∪ {ψ})).
    {
      induction el0; intros; simpl in H4.
      + invert_constructor_equalities; subst; split => //.
      + destruct n; [rewrite_anywhere foldLeft_constant => // |].
        simpl in H4.
        destruct (⟦ a ⟧ (σ1, ρ, ψ )( n)) eqn:A;
          try solve [rewrite_anywhere foldLeft_constant => //; try eval_not_success_list].
        unshelve epose proof (H n _ _ _ _ _ _ _ A _ _); try lia ; eauto with wf; destruct_and.
        assert (dom σ <= dom s) by eauto using PeanoNat.Nat.le_trans with pM.
        assert ((codom (v :: acc) ∪ {l0}) ⪽ s). {
          apply storeSubset_union; eauto with wf.
          apply storeSubset_add; split; eauto with wf.
          apply storeSubset_trans with σ1; eauto with wf pM.
          apply storeSubset_singleton2. eapply PeanoNat.Nat.lt_le_trans with (dom σ1); eauto with wf pM.
        }
        apply  IHel0 in H4; eauto using PeanoNat.Nat.le_trans, preserving_transitivity_degenerate with wf pM .
        apply scopability_add ; eauto.
        ++ apply scoping_transitivity with σ1 (codom ρ ∪ {ψ}); eauto with pM wf.
           apply H7; eauto with pM wf scoping.
        ++ apply H11; eauto with pM wf .
           apply H7; eauto with pM wf scoping.
    }
    eapply H4 in H0; eauto with wf pM; try rewrite codom_empty_union => //.
    rewrite storeSubset_singleton2; eauto with wf.
  Qed.

  Lemma scopability_list_aux2:
    forall n : nat,
      (forall k : nat,
          k < S (S n) ->
          forall (e : Expr) (σ σ' : Store) (ρ : Env) (ψ l : Value),
            (⟦ e ⟧ (σ, ρ, ψ )( k)) = Success l σ' ->
            wf σ -> (codom ρ ∪ {ψ}) ⪽ σ -> ((σ, codom ρ ∪ {ψ}) ⋖ (σ', {l})) /\ (σ ⇝ σ' ⋖ codom ρ ∪ {ψ})) ->
      forall  σ ρ ψ ,
        wf σ ->
        (codom ρ ∪ {ψ}) ⪽ σ ->
        forall el σ1 σ2 L acc,
          fold_left (eval_list_aux ρ ψ n) el (Success_list acc σ1) = Success_list L σ2 ->
          wf σ1 ->
          dom σ <= dom σ1 ->
          (σ, codom ρ ∪ {ψ}) ⋖ (σ1, codom acc) ->
          (codom acc) ⪽ σ1 ->
          σ ⇝ σ1 ⋖ (codom ρ ∪ {ψ}) ->

          ((σ, codom ρ ∪ {ψ}) ⋖ (σ2, codom L)) /\
          (σ ⇝ σ2 ⋖ codom ρ ∪ {ψ}) /\
          (dom σ <= dom σ2) /\
          (codom L ⪽ σ2) /\
          (wf σ2).
  Proof.
    intros n H_strong σ ρ ψ H_wf H_codom.
    induction el; intros; simpl in H.
    + invert_constructor_equalities; subst => //.
    + destruct n; [rewrite_anywhere foldLeft_constant => // |].
      simpl in H.
      destruct (⟦ a ⟧ (σ1, ρ, ψ )( n)) eqn:A;
        try solve [rewrite_anywhere foldLeft_constant => //; try eval_not_success_list].
      unshelve epose proof (H_strong n _ _ _ _ _ _ _ A _ _); try lia ; eauto with wf; destruct_and.
      assert (dom σ1 <= dom s) by eauto with pM.
      assert (dom σ <= dom s) by lia.
      apply IHel in H; eauto using PeanoNat.Nat.le_trans, preserving_transitivity_degenerate with wf pM.
      ++ assert (codom (v::acc) = Union Loc (Singleton Loc v) (codom acc)). {
           apply Extensionality_Ensembles.
           unfold Same_set; steps; intros l'; steps; eauto using Union_introl, Union_intror.
           inversion H9; try inSingleton; steps.
         }
         rewrite_any.
         apply scoping_union; eauto.
         +++ eapply scoping_transitivity with σ1 (codom ρ ∪ {ψ}) ; eauto with wf.
             apply H4; eauto with wf pM scoping.
         +++ apply H6; eauto with wf pM.
             apply H4; eauto with wf pM scoping.
      ++ apply storeSubset_add; split; eauto with wf.
  Qed.

  Lemma scopability_add_env:
    forall I v s c e0,
      getObj s I = Some (c, e0) ->
      v < dom s ->
      forall σ0 L0 L2 ,
        L0 ⪽ σ0 ->
        L2 ⪽ s ->
        (σ0, L0) ⋖ (s, {v}) ->
        (σ0, L0) ⋖ (s, L2) ->

        (σ0, L0) ⋖ ([I ↦ (c, e0 ++ [v])] (s), L2).
  Proof.
    intros.
    unfold scoping; simpl; intros.
    unfold reachability_set in *. destruct H8 as [l2 [Hl2 Hrch]].
    assert (reachability s l2 l \/ (reachability s l2 I /\ reachability s v l)) as [Hrch2 | [HrchI Hrchl]] by
          eauto using reachability_add_env, getObj_dom.
    + eapply_any; simpl; eauto with wf.
      exists l2; steps.
    + eapply H3; simpl; eauto with wf.
      eapply storeSubset_singleton2 => //.
      exists v; steps.
  Qed.


  Lemma scopability_init:
    forall n,
      (forall k,
          k < S (S n) ->
          forall (e : Expr) (σ σ' : Store) (ρ : Env) (ψ l : Value),
            (⟦ e ⟧ (σ, ρ, ψ )( k)) = Success l σ' ->
            wf σ -> (codom ρ ∪ {ψ}) ⪽ σ -> ((σ, codom ρ ∪ {ψ}) ⋖ (σ', {l})) /\ (σ ⇝ σ' ⋖ codom ρ ∪ {ψ})) ->
      forall σ L L1 I fields σ1 σ2,
        fold_left (init_field L1 I n) fields (Some σ1) = Some σ2 ->

        dom σ <= dom σ1 ->
        I < dom σ1 ->
        wf σ1 ->
        (codom L1 ∪ {I}) ⪽ σ1 ->
        ((σ, L) ⋖ (σ1, (codom L1) ∪ {I})) ->
        (σ ⇝ σ1 ⋖ L) ->

        ((σ, L) ⋖ (σ2, (codom L1) ∪ {I})) /\ (σ ⇝ σ2 ⋖ L) /\ (dom σ1 <= dom σ2).
  Proof.
    intros n H_strong σ L L1 I.
    induction fields; intros; simpl in H.
    + invert_constructor_equalities; steps.
    + destruct n; [rewrite_anywhere foldLeft_constant => // |].
      simpl in H.
      destruct a as [_ e].
      destruct (⟦ e ⟧ (σ1, L1, I )( n)) eqn:E; try solve [rewrite_anywhere  foldLeft_constant => //].
      rewrite {2}/assign_new in H.
      destruct (getObj s I) eqn:G; try solve [rewrite_anywhere  foldLeft_constant => //].
      destruct o.
      unshelve epose proof (H_strong n _ _ _ _ _ _ _ E _ _); try lia ; eauto with wf; destruct_and.
      assert (dom [I ↦ (c, e0 ++ [v])] (s) = dom s) as H_dom_s by eauto using update_dom.
      assert (dom σ1 <= dom s) by eauto with pM.
      assert (wf s) by eauto with wf.
      eapply IHfields in H as [A1 [A2 A3]];
        repeat split; eauto with wf pM;
          try solve [eapply_any; eauto];
          try solve [rewrite H_dom_s || rewrite H_dom_s in A3; lia].
      ++ unfold wf; intros. rewrite H_dom_s.
         assert (I < dom s) by lia.
         destruct (PeanoNat.Nat.eq_dec l I) as [Heq | Hneq].
         +++ (* l = I *)
           subst.
           rewrite (getObj_update1 s (c, e0 ++ [v]) I _) in H10 => //.
           invert_constructor_equalities; subst.
           assert (f < length e0 \/ f = length e0) as Hf . {
             apply Lt.le_lt_or_eq, Lt.lt_n_Sm_le.
             pose proof (nth_error_Some (e0 ++ [v]) f) as Hf.
             rewrite app_length PeanoNat.Nat.add_1_r in Hf.
             apply Hf.
             unfold getVal in *.
             rewrite H11. steps.
           }
           destruct Hf; unfold getVal in *.
           ++++ rewrite_anywhere nth_error_app1; steps.
                eapply_any; eauto.
           ++++ rewrite nth_error_app2 in H11 ; steps.
                rewrite PeanoNat.Nat.sub_diag in H11. simpl in H11. invert_constructor_equalities; subst.
                eapply correct_value; eauto.
         +++ (* l <> I *)
           rewrite getObj_update2 in H10 => //. steps.
           eapply_any; eauto.
      ++ eapply storeSubset_trans with s; eauto with pM wf. rewrite H_dom_s => //.
      ++ eapply scoping_transitivity with σ1 _; try solve [eapply_any]; eauto with scoping.
         apply scopability_add_env; try lia; eauto with wf.
         eapply H7; eauto with scoping.
      ++ eapply preserving_transitivity; eauto.
         eapply preserving_transitivity; eauto.
         unfold scoping_preservation; split; intros; eauto using scopability_add_env with wf.
         eapply storeSubset_singleton2; eauto with wf.
  Qed.


  Lemma scopability_theorem:
    forall n, ScopabilityProp n.
  Proof.
    apply strong_induction. unfold ScopabilityProp.
    intros n H_strong2 e σ σ' ρ ψ l H_success H_wf H_codom.
    destruct n => //.
    move: (H_strong2 n (le_n (S n)) ) => H_strong.
    destruct e as [x | this | e0 f | e0 m el | C el | e0 f e1 e2];
      simpl in H_success; repeat destruct_match;
        try discriminate;
        try invert_constructor_equalities; subst.
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
        eauto using getObj_dom with rch.
        eapply rch_step; eauto.
        eapply wellformedness_conserved in matched0; eauto.
      }
      assert ((σ,  (codom ρ) ∪ (Singleton Loc ψ)) ⋖ (σ', {l})) as C1. {
      apply (scoping_transitivity _ σ' _ _ {v}) => //.
      unfold storeSubset. intros. inSingleton. eauto using getObj_dom.
      }
      steps.
    + (* e = e0.m(l0) *)
      destruct n; try discriminate.
      rename matched into A1, s into σ0, l0 into ρ', v into l0, e into ω, matched0 into A5,
      s0 into σ_n, body into e_m, H_success into E0, l into l_m, σ' into σ_m, matched6 into B0.
      assert (dom σ <= dom σ_n) by eauto using PeanoNat.Nat.le_trans with pM.
      pose proof (H_strong _ _ _ _ _ _ A1 H_wf H_codom) as [A2 A3].
      assert ((σ, (codom ρ) ∪ {ψ}) ⋖ (σ0, (codom ρ) ∪ {ψ})) as A4
          by eauto using  preserving_regularity_degenerate, PartialMonotonicity.partialMonotonicity_theorem_dom.
      move: A1 A2 A3 A4 A5 => A1 A2 A3 A4 A5.
      assert ((wf σ_n) /\ (codom ρ' ∪ {l0}) ⪽ σ_n) as [H_wf_n H_codom']. {
        split; try eapply storeSubset_union;
          try (
              unfold storeSubset; intros; inSingleton;
              eapply PeanoNat.Nat.lt_le_trans with (dom σ0); eauto using getObj_dom);
          try solve [ eapply wellformedness_theorem_list_aux; eauto with wf;
                      eapply storeSubset_trans ; try eapply A3; eauto with pM].
      }
      move: (H_strong _ _ _ _ _ _ E0 H_wf_n H_codom') => [E1 E2].
      move: (scopability_list_aux _ H_strong2 _ _ _ _ _ _ _ _ _ B0 H_wf H_codom A1) => [F1 F2].
      split ; eauto with scoping.
    + (* e = new C(l0) *)
      destruct n; try discriminate.
      simpl in matched0. repeat (destruct_match; try discriminate).
      simpl in matched.


      rename matched into C0, s into σ_n, l0 into L.

      assert (((σ, codom ρ ∪ {ψ}) ⋖ (σ_n, codom L)) /\
              (σ ⇝ σ_n ⋖ codom ρ ∪ {ψ}) /\
              (dom σ <= dom σ_n) /\ (codom L ⪽ σ_n) /\ wf σ_n) as [C1 [C2 [C3 [C4 C5]]]]. {
        eapply scopability_list_aux2; eauto with wf.
        + unfold scoping; simpl; intros. unfold reachability_set in *. destruct_exists. steps.
        + unfold scoping_preservation; steps.
      }
      assert (dom (σ_n++[(C,[])]) = S (dom σ_n)) by (unfold dom; rewrite app_length; steps; lia).
      assert (((σ, codom ρ ∪ {ψ}) ⋖ (σ', codom L ∪ {length σ_n})) /\
              (σ ⇝ σ' ⋖ codom ρ ∪ {ψ}) /\
              dom (σ_n ++ [(C, [])]) <= dom σ')
        as [D1 [D2 D3]]. {
        apply (scopability_init n H_strong2 σ (codom ρ ∪ {ψ}) _ _ _ _ _ matched0); eauto with wf; try lia.
        ++ unfold dom; rewrite app_length; steps; lia.
        ++ apply storeSubset_union; eauto with wf.
           eapply storeSubset_trans with (σ_n); eauto; try (rewrite H; lia).
           apply storeSubset_singleton2. rewrite H; unfold dom in *; lia.
        ++ unfold scoping; simpl; intros.
           unfold reachability_set in *. Opaque eval. steps.
           inversion H4.
           +++ apply C1; steps.
               eapply reachability_empty; eauto using PeanoNat.Nat.lt_le_trans.
               eexists; split; eauto using Union_introl.
           +++ inSingleton. apply C1; eauto using reachability_empty.
               apply_anywhere reachability_not_empty => //.
               eauto using PeanoNat.Nat.lt_le_trans.
        ++ eapply preserving_transitivity; eauto.
           unfold scoping_preservation; split; intros; eauto.
           unfold scoping; simpl; intros.
           assert (reachability_set σ_n L1 l) by eauto using PeanoNat.Nat.lt_le_trans, reachability_empty.
           steps.
      }
      rewrite H in D3.
      split => //.
      eapply scoping_union_intror; eauto with wf scoping.
      eapply storeSubset_union; [
        eapply storeSubset_trans with σ_n => //; lia |
        apply storeSubset_singleton2; unfold dom in *; lia ].
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
  Qed.

End Scopability.
