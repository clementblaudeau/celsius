From Celsius Require Export Trees.
From Celsius Require Export Eval.
From Celsius Require Export PartialMonotonicity.
From Celsius Require Export Reachability.
From Celsius Require Export Compatibility.
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

Module Wellformedness.
  Import Eval.Evaluator.

  Definition wf σ := forall l C ω, getObj σ l = Some(C,ω) -> forall f l, getVal ω f = Some l -> l < dom σ.

  Definition storeSubset (σ: Store) L := (forall l, (l ∈ L) -> l < (dom σ)).
  Notation "L ⪽ σ" := (storeSubset σ L) (at level 80).
  Definition codom (ρ: Env) : (LocSet):=
    fun (l: Loc) => (List.In l ρ).

  Lemma storeSubset_trans : forall a s s', dom s <= dom s' -> a ⪽ s -> a ⪽ s'.
  Proof.
    intros. intros l Hl.
    pose proof (H0 l Hl).
    lia.
  Qed.

  Lemma storeSubset_union : forall a b s, a ⪽ s -> b ⪽ s -> (a∪b) ⪽ s.
  Proof.
    unfold storeSubset; intros.
    induction H1; eauto.
  Qed.


  Lemma storeSubset_add : forall v a s,
      codom (v :: a) ⪽ s <-> v < dom s /\ codom a ⪽ s.
  Proof.
    split; intros.
    + unfold storeSubset in H.
      split. apply H.
      unfold codom, List.In, In; left => //.
      intros l Hl. apply H.
      unfold codom, List.In, In; right => //.
    + intros l Hl. unfold codom, List.In, In in Hl. move: Hl=> [Hl|Hl]; steps.
  Qed.

  Notation " a ∪ { b } " := (Union Loc a (Singleton Loc b)) (at level 80).
  Lemma storeSubset_singleton : forall a b σ, a ∪ {b} ⪽ σ -> b < dom σ.
  Proof.
    intros. apply (H b).
    eauto using Union_intror, In_singleton.
  Qed.

  Lemma storeSubset_codom_empty : forall s, codom [] ⪽ s.
  Proof.
    intros s l Hl.
    steps.
  Qed.

  Lemma wf_add : forall s c ρ, wf s -> codom ρ ⪽ s -> wf (s ++ [(c,ρ)]).
  Proof.
    unfold wf, dom; intros.
    pose proof (getObj_dom _ _ _ H1).
    pose proof (PeanoNat.Nat.eq_dec l (length s)) as [Hl0 | Hl0].
    + rewrite app_length. simpl. subst.
      rewrite getObj_last in H1. invert_constructor_equalities; subst.
      rewrite PeanoNat.Nat.add_1_r. apply (PeanoNat.Nat.lt_trans _ (length s) _); try lia.
      apply H0.
      unfold getVal in H2. apply nth_error_In in H2. eauto.
    + unfold dom in *. rewrite_anywhere app_length. simpl in H2.
      rewrite PeanoNat.Nat.add_1_r in H3.
      apply (PeanoNat.Nat.lt_succ_r l (length s)) in H3.
      assert (l < length s) by lia.
      rewrite app_length. simpl. unfold getObj in *.
      rewrite nth_error_app1 in H1 => //.
      apply (H _ _ _ H1) in H2. lia.
  Qed.

  Lemma wf_add_empty : forall s c, wf s -> wf (s ++ [(c,[])]).
  Proof.
    eauto using wf_add, storeSubset_codom_empty.
  Qed.


  Lemma wf_assign: forall σ σ' ω ω' l v f C,
      (getObj σ l) = Some (C, ω) ->
      σ' = [l ↦ (C, ω')]σ ->
      ω' = [f ↦ v]ω ->
      v < dom σ ->
      wf σ -> wf σ'.
  Proof.
    unfold wf; steps. rewrite update_dom.
    pose proof (PeanoNat.Nat.eq_dec l l0) as [Hl0 | Hl0]; subst.
    + rewrite getObj_update1 in H4; eauto using getObj_dom.
      unfold getVal in *.
      assert (f0 < length ω0). {
        pose proof (nth_error_Some ω0 f0);
        destruct (nth_error ω0 f0); eapply_any; steps.
      }
      invert_constructor_equalities; subst.
      pose proof (PeanoNat.Nat.eq_dec f f0) as [Hf | Hf]; subst.
      ++ rewrite_anywhere update_one3.
         rewrite update_one1 in H5 => // .
         invert_constructor_equalities; steps.
      ++ erewrite update_one2 in H5; eauto.
    + unfold getObj in *.
      rewrite update_one2 in H4; eauto using PeanoNat.Nat.neq_sym.
  Qed.



  Theorem wellformedness_theorem_list_aux : forall k n ρ ψ,
      (forall k : nat,
          k < n ->
          forall (e : Expr) (σ σ' : Store) (ρ : Env) (ψ l : Value),
            (⟦ e ⟧ (σ, ρ, ψ )( k)) = Success l σ' -> wf σ -> (codom ρ ∪ {ψ}) ⪽ σ -> wf σ' /\ l < dom σ') ->
      k < n ->
      forall el s s' vl1 vl2,
        fold_left (eval_list_aux ρ ψ k) el (Success_list vl1 s) = Success_list vl2 s' ->
        wf s ->
        codom vl1 ⪽ s ->
        (codom ρ ∪ {ψ}) ⪽ s ->
        wf s' /\ (codom vl2 ⪽ s') /\ (dom s <= dom s').
  Proof.
    intros k n ρ ψ H_strong Hn.
    induction el; simpl; intros; try solve [steps].
    destruct k => //; try solve [rewrite foldLeft_constant in H => //].
    simpl in H.
    destruct (⟦ a ⟧ (s, ρ, ψ )( k)) eqn:A ; try solve [rewrite foldLeft_constant in H => //] ;
      try solve [eval_not_success_list].
    apply PeanoNat.Nat.lt_succ_l in Hn.
    pose proof (H_strong k Hn _ _ _ _ _ _ A H0 H2) as [Hwfs2 Hv0].
    pose proof (PartialMonotonicity.partialMonotonicity_theorem_dom _ _ _ _ _ _ _ A).
    assert (codom (v :: vl1) ⪽ s0). by (apply storeSubset_add; eauto using storeSubset_trans).
    move /(_ _ _ _ _ H Hwfs2 H4 (storeSubset_trans _ s s0 H3 H2)): IHel => IHel.
    steps; try lia.
  Qed.


  Theorem wellformedness_conserved :
    forall k e σ σ' ρ ψ l, ⟦e⟧(σ, ρ, ψ)(k) = (Success l σ') -> wf σ -> (codom ρ) ∪ {ψ} ⪽ σ -> (wf σ' /\ l < dom σ').
    apply (strong_induction (fun k => forall e σ σ' ρ ψ l, ⟦e⟧(σ, ρ, ψ)(k) = (Success l σ') -> wf σ -> (codom ρ) ∪ {ψ} ⪽ σ ->  (wf σ' /\ l < dom σ'))). intros.
    assert (ψ < dom σ /\ forall l', List.In l' ρ -> l' < dom σ). {
      unfold storeSubset in *.
      split; steps; eauto using Union_introl, Union_intror, In_singleton. }
    destruct_and.
    destruct n => //.
    move : (PeanoNat.Nat.lt_succ_diag_r n) => Hn.
    destruct e ; simpl in H0 ;
      repeat discriminate || subst || invert_constructor_equalities || destruct_match ||
             lazymatch goal with
             | H1 : ⟦ _ ⟧ ( _, _, _)( _ ) = Success _ _ |- _ =>
               pose proof (PartialMonotonicity.partialMonotonicity_theorem_dom _ _ _ _ _ _ _ H1);
                 pose proof (H n Hn _ _ _ _ _ _ H1); clear H1 end; eauto.


    + intuition auto. eauto using nth_error_In.
    + intuition auto. unfold wf in *. eapply H6; eauto.
    + destruct n => //. simpl in *.
      apply PeanoNat.Nat.lt_succ_l in Hn.
      pose proof (wellformedness_theorem_list_aux n (S(S n)) ρ ψ H Hn _ _ _ _ _ matched3) as H_list.
      assert (codom [] ⪽ s) by done.
      assert ((codom ρ ∪ {ψ}) ⪽ s) by eauto using storeSubset_trans.
      apply H6; intuition auto.
      intros l2 Hl2; induction Hl2; eauto.
      induction H6. lia.
    + destruct n => //. simpl in *.
      apply PeanoNat.Nat.lt_succ_l in Hn.
      pose proof (wellformedness_theorem_list_aux n (S(S n)) ρ ψ H Hn _ _ _ _ _ matched H1 (storeSubset_codom_empty _) H2) as [H_wf_s [H_codom_s H_dom_s]].
      repeat destruct_match; try discriminate.
      assert (forall k fields l σ1 σ2,
                 k < S (S n) ->
                 fold_left (init_field l1 l k) fields (Some σ1) = Some σ2 ->
                 (codom l1 ∪ {l}) ⪽ σ1 ->
                 wf σ1 ->
                 wf σ2 /\ (dom σ1 <= dom σ2)). {
        induction fields0; simpl; intros; try solve [steps].
        destruct k; simpl in H5; try solve [rewrite_anywhere foldLeft_constant  => //].
        destruct a.
        destruct (⟦ expr ⟧ (σ1, l1, l )(k)) eqn: E; try solve [rewrite_anywhere foldLeft_constant  => //].
        unfold assign_new in *. destruct_match; try solve [rewrite_anywhere foldLeft_constant  => //].
        destruct o.
        pose proof (PartialMonotonicity.partialMonotonicity_theorem_dom _ _ _ _ _ _ _ E).
        apply H in E => // ; try lia. destruct E as [E1 E2].
        apply IHfields0 in H5; clear IHfields0 => //.
        ++ steps. unfold dom in *; rewrite_anywhere update_one3. eauto using PeanoNat.Nat.le_trans.
        ++ apply (storeSubset_trans _ σ1 s0) in H6 => //.
           apply (storeSubset_trans _ s0) => //.
           unfold dom in *.
           rewrite update_one3; eauto.
        ++ clear H5.
           intros l'; intros.
           unfold dom in *. rewrite update_one3.
           move: (PeanoNat.Nat.eq_dec l l') => [Hl' | Hl'].
           +++ (* l = l' *)
             subst.
             rewrite getObj_update1 in H5; eauto using getObj_dom. invert_constructor_equalities; subst.
             unfold getVal in *. apply nth_error_Some2 in H9. destruct H9 as [H9 | H9]; subst; eauto.
           +++ (* l ≠ l' *)
             unfold getObj in *.
             rewrite update_one2 in H5 => //. eapply E1; eauto.
        }
      apply H0 in matched0; eauto using wf_add_empty.
      split; steps.
      unfold dom in *; rewrite_anywhere app_length. simpl in *. lia.
      apply storeSubset_union. apply (storeSubset_trans _ s _) => //. unfold dom in *; rewrite app_length; lia.
      unfold storeSubset; intros. induction H5. unfold dom in *; rewrite app_length; simpl ; lia.
    + unfold assign in *.
      destruct (getObj s0 v0) eqn:G.
      ++ destruct o.
         apply H6. intuition auto.
         eapply wf_assign; eauto; try eapply H9; eauto using storeSubset_trans.
         apply (storeSubset_trans _ σ _) => //.
         unfold dom in *; rewrite update_one3. lia.
      ++ repeat apply_any; eauto using storeSubset_trans.
  Qed.



End Wellformedness.
