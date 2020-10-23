From Celsius Require Export Trees.
From Celsius Require Export Eval.
Require Import ssreflect ssrbool.

Require Import Coq.Arith.Wf_nat.
Require Import Coq.Wellfounded.Wellfounded.
Require Import List.
Import ListNotations.
Open Scope nat_scope.
Open Scope list_scope.
Require Import Sets.Ensembles.

Module Reachability.
  Import Eval.Evaluator.

  (* Reserved Notation "σ ⊨ l1 ⇝ l2" (at level 80). *)
  Inductive reachability : Store -> Loc -> Loc ->Prop :=
  |rch_heap  : forall l σ,  l < (dom σ) -> (reachability σ l l)
  |rch_trans : forall l0 l1 l2 C ω σ, (reachability σ l0 l1) -> (getObj σ l1 = Some (C, ω)) -> (exists f, (getVal ω f = Some l2)) -> (l2 < dom σ) -> (reachability σ l0 l2).
  Notation "σ ⊨ l1 ⇝ l2" := (reachability σ l1 l2) (at level 80, l1 at level 80, l2 at level 80).

  Definition reachability_set σ (L: LocSet) l := exists l', (l' ∈ L) /\ (σ ⊨ l' ⇝ l).
  Notation "σ ⊫ L ⇝ l" := (reachability_set σ L l) (at level 80, l at level 99, L at level 99).

  Definition reachable_cold (σ: Store) (l: Loc) := (l < dom σ).
  Notation "σ ⊨ l : 'cold'" := (reachable_cold σ l) (at level 80, l at level 80).
   Notation "σ ⊫ L : 'cold'" := (forall l, (l ∈ L) -> reachable_cold σ l) (at level 80, L at level 99).

  Definition reachable_warm (σ: Store) (l: Loc) := (exists C ω args fields methods , (getObj σ l) = Some (C, ω) /\ ((ct C) = Some (class args fields methods)) /\ (length fields <= length ω)).
  Notation "σ ⊨ l : 'warm'" := (reachable_warm σ l) (at level 80, l at level 80).
  Notation "σ ⊫ L : 'warm'" := (forall l, (l ∈ L) -> reachable_warm σ l) (at level 80, L at level 99).

  Definition reachable_hot  (σ: Store) (l: Loc) :=(forall (l': Loc), (σ ⊨ l ⇝ l') -> (σ ⊨ l' : warm)).
  Notation "σ ⊨ l : 'hot'"  := (reachable_hot σ l) (at level 80, l at level 80).
  Notation "σ ⊫ L : 'hot'" := (forall l, (l ∈ L) -> reachable_hot σ l) (at level 80, L at level 99).

  Lemma reachability_trans: (forall σ l1 l2 l3, (σ ⊨ l1 ⇝ l2) -> (σ ⊨ l2 ⇝ l3) -> (σ ⊨ l1 ⇝ l3)).
  Proof.
    intros σ l1 l2 l3 H1 H2.
    induction H2 => //.
    apply (rch_trans l1 l2 l3 C ω σ (IHreachability H1) H H0 H3).
  Qed.
  Lemma reachability_hot: forall (σ: Store) (l l': Loc), σ ⊨ l: hot -> σ ⊨ l ⇝ l' -> σ ⊨ l': hot.
  Proof.
    intros σ l l' H1 H2 l'' H3.
    apply (H1 l'' ((reachability_trans _ _ _ _) H2 H3)).
  Qed.

  Lemma reachability_singleton : forall σ l1 l2, (σ ⊫ (Singleton Loc l1) ⇝ l2) <-> σ ⊨ l1 ⇝ l2.
  Proof.
    split; intros.
    unfold reachability_set in H. repeat destruct H => //.
    exists l1 => //.
  Qed.

  Lemma reachability_dom : forall σ l1 l2, (σ ⊨ l1 ⇝ l2) -> (l1 < (dom σ)) /\ (l2 < (dom σ)).
    intros.
    induction H; steps.
  Qed.


  Lemma reachability_weaken_assignment :
    forall σ σ' C ω ω' s e f l l',
      (getObj σ l) = Some (C, ω) ->
      ω' = [f ↦ l']ω ->
      σ' = [l ↦ (C, ω')]σ ->
      (l = l') ->
      σ' ⊨ s ⇝ e ->
      σ ⊨ s ⇝ e.
  Proof.
    intros. move: H3. move: s e. induction 1; repeat steps || rewrite_anywhere update_dom.
    + apply rch_heap => //.
    + eapply reachability_trans; eauto.
      destruct (PeanoNat.Nat.eq_dec l1 l'); subst; [apply_anywhere update_one4; steps |].
      ++ destruct (PeanoNat.Nat.eq_dec f f0); subst; [apply_anywhere update_one4; steps |]; eauto using rch_heap.
         unfold getVal in *.
         rewrite update_one2 in H0; eauto.
         eapply rch_trans; try apply rch_heap; eauto using getObj_dom.
      ++ rewrite getObj_update2 in H4; eauto using getObj_dom.
         eapply rch_trans; try apply rch_heap; eauto using getObj_dom.
  Qed.

  (* Notions of path into the heap *)

  Definition reachable_one_step σ l0 l1 :=
    exists C ω, (getObj σ l0 = Some (C, ω)) /\ (exists f, (getVal ω f = Some l1)) /\ (l1 < dom σ).

  Lemma reachable_one_step_reachability :
    forall σ l0 l1, reachable_one_step σ l0 l1 -> σ ⊨ l0 ⇝ l1.
  Proof.
    unfold reachable_one_step; steps.
    eauto using rch_trans, rch_heap, getObj_dom.
  Qed.

  (* Path in σ (p is in reverse order) *)
  Fixpoint reachable_path σ p {struct p}:=
    match p with
    | [] => True
    | l1::nil => l1 < dom σ
    | l2::((l1::_) as p') => reachable_one_step σ l1 l2 /\ reachable_path σ p'
    end.

  Ltac destructs :=
    repeat subst ||
    match goal with
    | H : _ \/ _ |- _ => let fresh1 := fresh H in
                      let fresh2 := fresh H in destruct H as [fresh1 | fresh2]
    | H : _ /\ _ |- _ => let fresh1 := fresh H in
                      let fresh2 := fresh H in destruct H as [fresh1 fresh2]
    | H : exists a, _  |- _ => let fresh a := fresh a in destruct H as [a H]
    end.


  Lemma reachable_path_reachability:
    forall σ s e,
      ((s = e /\ s < dom σ) \/ exists p, reachable_path σ (e :: (p++[s]))) <-> σ ⊨ s ⇝ e.
  Proof.
    split.
    + intros [[H1 H2] | [p Hp]]; subst; eauto using rch_heap.
      generalize dependent e.
      generalize dependent s.
      induction p; repeat light; eauto using reachable_one_step_reachability.
      specialize (IHp s a).
         unfold reachable_one_step in H. destructs.
         eapply rch_trans; eauto.
    + induction 1 ; [steps | destructs].
      ++ right. exists []. simpl; unfold reachable_one_step; steps.
         repeat eexists; eauto.
      ++ right. exists (l1::p); simpl.
         split; eauto.
         eexists; eexists; eauto.
  Qed.

  Lemma reachable_path_is_reachable:
    forall σ e p l,
      reachable_path σ (e::p) ->
      List.In l (e::p) ->
      σ ⊨ l ⇝ e.
  Proof.
    intros σ e p.
    generalize dependent e.
    induction p ; try solve [repeat light ; eauto using rch_heap].
    intros. simpl in H0. destruct H0 as [H0 | H0]; subst.
    + subst; simpl in H.
      destruct p eqn:P ; repeat light; eauto using rch_heap, reachable_one_step_reachability, reachability_dom;
      apply reachable_one_step_reachability, reachability_dom in H0; apply rch_heap; steps.
    + specialize (IHp a l).
      destruct p eqn:P; [steps; eauto using reachable_one_step_reachability |].
      rewrite <- P in *. simpl in H.
      destruct_and.
      unfold reachable_one_step in H.
      destructs;
      eapply rch_trans; eauto;
      eapply IHp; simpl; eauto.
  Qed.

  Lemma reachable_path_last:
    forall σ s1 s2 p,
      reachable_path σ (p++[s2;s1]) ->
      reachable_path σ (p++[s2]).
  Proof.
    intros.
    induction p; simpl in *.
    + unfold reachable_one_step in * ; steps.
    + destruct_match; [ apply_anywhere app_eq_nil; steps | ].
      destruct_match; [ apply_anywhere app_eq_nil; steps | ].
      assert ( n = n0) by (destruct p; steps); steps.
  Qed.


  Lemma reachable_path_app:
    forall σ s1 s2 p1 p2,
      reachable_path σ (p2++s2::p1++[s1]) ->
      reachable_path σ (s2::p1++[s1]) /\ reachable_path σ (p2++[s2]).
  Proof.
    split; intros.
    + generalize dependent s1.
      generalize dependent s2.
      generalize dependent p1.
      induction p2; simpl.
      ++ destruct p1; steps.
      ++ intros. repeat ( destruct_match; [apply_anywhere app_eq_nil; steps |]).
         rewrite <- matched in *.
         rewrite <- matched0 in *.
         destructs.
         apply IHp2 in H1. simpl in H1.
         steps.
    + assert (forall l p s, reachable_path σ (p++s::l) -> reachable_path σ (p++[s])); eauto.
      induction l; steps.
      specialize (IHl (p++[s]) a).
      eapply reachable_path_last.
      repeat rewrite <- app_assoc in *.
      simpl in *; eauto.
  Qed.

  Lemma app_exists_last:
    forall p (x:Loc),
    exists y p', x::p = p'++[y].
  Proof.
      induction p; steps.
      + exists x, []; steps.
      + move /(_ a):IHp => IHp. steps.
        exists y, (x::p'); steps.
  Qed.


  Lemma reachable_path_app2:
    forall σ s p1 p2,
      reachable_path σ (p2++s::p1) ->
      reachable_path σ (p2++[s]).
  Proof.
    assert (
        forall (σ : list Obj) (s s': nat) (p1 p2 : list nat),
          reachable_path σ (p2 ++ s :: p1++[s']) -> reachable_path σ (p2 ++ [s])) by
        repeat steps || eapply_anywhere reachable_path_app.
    intros.
    pose proof app_exists_last.
    destruct p1 => //.
    move /(_ p1 n):H1 => H1; steps.
    rewrite H1 in H0; eauto.
  Qed.

  Definition contains_edge p (l1 l2 :Loc) :=
    exists p1 p2, p = p2 ++ l2::l1::p1.


  Lemma contains_edge_dec :
    forall p l1 l2, contains_edge p l1 l2 \/ not (contains_edge p l1 l2).
  Proof.
    unfold contains_edge. intros.
    induction p; steps.
    + right. steps. symmetry in H. apply app_eq_nil in H. steps.
    + left. exists p1, (a::p2); steps.
    + pose proof (PeanoNat.Nat.eq_dec a l2) as [Ha | Ha].
      ++ (* a = l2 *)
        subst.
        destruct p; steps.
        +++ right; steps. symmetry in H0. apply app_eq_unit in H0; steps.
        +++ pose proof (PeanoNat.Nat.eq_dec l l1) as [Hl | Hl].
            ++++ left; steps.
                 exists p, []; steps.
            ++++ right; steps. destruct p2; steps; eauto.
      ++ right; steps.
         destruct p2; steps; eauto.
  Qed.

  Lemma contains_edge_cons :
    forall p l l' l0,
      contains_edge (l0::p) l l' ->
      l' <> l0 ->
      contains_edge p l l'.
  Proof.
    unfold contains_edge; steps.
    destruct p2; steps; eauto.
  Qed.


  Lemma reachable_path_split_on_edge:
    forall σ s p l1 l2,
      reachable_path σ (p++[s]) ->
      contains_edge p l1 l2 ->
      σ ⊨ s ⇝ l1.
  Proof.
    unfold contains_edge; steps.
    generalize dependent l1.
    generalize dependent l2.
    generalize dependent p1.
    induction p2; intros.
    + rewrite_anywhere app_nil_l.
      simpl in *.
      eapply reachable_path_is_reachable; destructs; eauto.
      rewrite app_comm_cons. apply in_app_iff; steps.
    + simpl in H.
      destruct_match; [apply_anywhere app_eq_nil; steps |].
      rewrite <- matched in *. destructs; eauto.
  Qed.


  Lemma contains_edge_assignment :
    forall σ σ' C ω ω' p f l l',
      (getObj σ l) = Some (C, ω) ->
      ω' = [f ↦ l']ω ->
      σ' = [l ↦ (C, ω')]σ ->
      not (contains_edge p l l') ->
      reachable_path σ' p ->
      reachable_path σ p.
  Proof.
    intros.
    generalize dependent p.
    induction p as [| l2 p]; intros; simpl; eauto.
    destruct p as [| l1 p]; [ simpl in *; subst; unfold dom in *; rewrite_anywhere update_one3; eauto |].
    simpl in H3. destruct_and.
    split.
    + unfold reachable_one_step in *; destructs.
      destruct H3 as [C0 [ω0 [H31 [[f0 H32] H33]]]].
      epose proof (getObj_dom _ _ _ H31).
      repeat rewrite_anywhere update_dom.
      destruct (PeanoNat.Nat.eq_dec l1 l); subst.
      ++ rewrite_anywhere getObj_update1; eauto. invert_constructor_equalities; subst.
         destruct (PeanoNat.Nat.eq_dec l2 l'); subst ; [exfalso; apply H2; exists p, []  ; steps |].
         unfold getVal in *. exists C0, ω; repeat split; eauto.
         destruct (PeanoNat.Nat.eq_dec f f0); subst; rewrite_anywhere  update_one2; eauto.
         apply_anywhere update_one4; subst. congruence.
      ++ rewrite_anywhere getObj_update2; eauto using getObj_dom.
         repeat eexists || split || eauto.
    + apply IHp; eauto.
      intros [p1 [p2 Hedge]].
      apply H2. exists p1, (l2::p2).
      rewrite Hedge; eauto.
  Qed.

  Lemma contains_edge_first_edge :
    forall p l l',
      contains_edge p l l' ->
      exists p1 p2, p = p1++(l'::l::p2) /\ not (contains_edge p2 l l').
  Proof.
    induction p as [p IHp] using (induction_ltof1 _ (fun x => length x)); unfold ltof in IHp.
    intros l l' [p1 [p2 H]].
    destruct (contains_edge_dec p1 l l').
    + apply IHp in H0.
      destruct H0 as [p3 [p4 [H01 H02]]].
      subst. exists (p2 ++ l' :: l :: p3), p4; split; eauto.
      repeat rewrite app_comm_cons || rewrite app_assoc => //.
      subst. rewrite app_length; simpl. Psatz.lia.
    + exists p2, p1; split; eauto.
  Qed.

  Lemma contains_edge_last_edge :
    forall p l l',
      contains_edge p l l' ->
      exists p1 p2, p = p1++(l'::l::p2) /\ not (contains_edge p1 l l').
  Proof.
    induction p as [p IHp] using (induction_ltof1 _ (fun x => length x)); unfold ltof in IHp.
    intros l l' [p1 [p2 H]].
    destruct (contains_edge_dec p2 l l').
    + apply IHp in H0.
      destruct H0 as [p3 [p4 [H01 H02]]].
      subst. exists p3 , (p4 ++ l' :: l :: p1) ; split; eauto.
      repeat rewrite app_comm_cons || rewrite app_assoc => //.
      subst. rewrite app_length; simpl. Psatz.lia.
    + exists p2, p1; split; eauto.
  Qed.

  Lemma reachable_path_assignment :
    forall σ σ' C ω ω' p f l l',
      (getObj σ l) = Some (C, ω) ->
      ω' = [f ↦ l']ω ->
      σ' = [l ↦ (C, ω')]σ ->
      reachable_path σ' p ->
      contains_edge p l l' \/ reachable_path σ p.
  Proof.
    intros.
    pose proof (contains_edge_dec p l l') as [Hedge | Hedge]; eauto.
    right.
    induction p; eauto.
    (* pose proof (PeanoNat.Nat.eq_dec a l') as [Ha | Ha]. *)
    simpl in H2.
    destruct_match; [steps ; unfold dom in *; rewrite_anywhere update_one3 => // |].
    subst. destructs. intuition auto. simpl.
    split.
    + clear H2. clear H1. unfold reachable_one_step in *; steps.
      destruct (PeanoNat.Nat.eq_dec l n); steps.
      ++ rewrite_anywhere getObj_update1; eauto using getObj_dom.
         invert_constructor_equalities; steps.
         repeat eexists || eassumption. unfold getVal in *.
         destruct (PeanoNat.Nat.eq_dec f f0); steps.
         +++ rewrite_anywhere update_one1 ; eauto using nth_error_Some.
             invert_constructor_equalities; steps.
             exfalso; apply Hedge.
             unfold contains_edge. exists l0, []; steps.
             erewrite <- update_one3.
             eapply nth_error_Some.
             erewrite H0 => //.
         +++ rewrite_anywhere update_one2; eauto .
         +++ unfold dom in *. erewrite_anywhere update_one3; eauto.
      ++ rewrite_anywhere getObj_update2; eauto using getObj_dom.
         repeat eexists || eassumption.
         unfold dom in *. erewrite <- update_one3; eauto.
    + apply H2; clear H2.
      unfold reachable_one_step, contains_edge in *.
      intros. destructs.
      apply Hedge. exists p1, (a::p2). rewrite H2.
      rewrite app_comm_cons => //.
  Qed.





End Reachability.
