From Celsius Require Export Trees.
From Celsius Require Export Eval.
Require Import ssreflect ssrbool.

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


  Definition reachable_one_step σ l0 l1 :=
    exists C ω, (getObj σ l0 = Some (C, ω)) /\ (exists f, (getVal ω f = Some l1)) /\ (l1 < dom σ).

  Lemma reachable_one_step_reachability :
    forall σ l0 l1, reachable_one_step σ l0 l1 -> σ ⊨ l0 ⇝ l1.
  Proof.
    unfold reachable_one_step; steps.
    eauto using rch_trans, rch_heap, getObj_dom.
  Qed.

  (* Path in σ to e (p is in reverse order) *)
  Fixpoint reachable_path σ e p :=
    match p with
    | l::nil => (* p = [l] *)
      l = e /\ e < dom σ
    | l::p' => (* p = p'++[l] *)
      (reachable_one_step σ l e) /\ (reachable_path σ l p')
    | _ => False
    end.

  Lemma reachable_path_reachability:
    forall σ s e,
      (exists p, reachable_path σ e (p++[s])) <-> σ ⊨ s ⇝ e.
  Proof.
    split.
    + intros [p Hp].
      generalize dependent e.
      induction p; repeat light; eauto using rch_heap.
      destruct_match; [destruct p; steps | repeat light].
      unfold reachable_one_step in H. move: H => [C [ω H]]. light.
      eapply rch_trans; eauto.
    + induction 1; steps.
      ++ exists []; simpl; eauto.
      ++ exists (l1::p); simpl. destruct (p++[l0]) eqn:P ; [destruct p ; steps | idtac].
         rewrite P; rewrite <- P.
         split; eauto.
         unfold reachable_one_step.
         eexists; eexists; eauto.
  Qed.

  Lemma reachable_path_is_reachable:
    forall σ e p l,
      reachable_path σ e p ->
      List.In l p ->
      σ ⊨ l ⇝ e.
  Proof.
    intros σ e p.
    generalize dependent e.
    induction p ; try solve [repeat light].
    intros. simpl in H0. destruct H0 as [H0 | H0].
    + subst; simpl in H.
      destruct p eqn:P ; repeat light; eauto using rch_heap, reachable_one_step_reachability.
    + simpl in H.
      destruct p eqn:P; eauto using in_nil.
      rewrite <- P in *.
      destruct_and.
      unfold reachable_one_step in *.
      Opaque reachable_path.
      move: H => [C [ ω [ Hobj [[f H] Hdom]] ] ] .
      eapply IHp in H1; eauto using rch_trans.
  Qed.


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





  (* Notions of path into the heap *)



End Reachability.
