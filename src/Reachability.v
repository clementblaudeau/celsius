(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the notion of reachability of a location in a given store. The set of reachable locations, starting from a given one l is transitively defined as the ones that can be accessed by following pointers in object local environments. We then define and prove basic properties around this notion. In the second part, we show the equivalence between the inductive definition and a path-based definition. This allows us to reason about paths from one location to another, especially for scopability results.  *)
From Celsius Require Export Eval Trees.
Require Import ssreflect ssrbool Coq.Arith.Wf_nat Coq.Wellfounded.Wellfounded List Psatz.
Import ListNotations.
Require Import Sets.Ensembles.
Open Scope nat_scope.
Open Scope list_scope.


(** ** Definitions and notations *)
(** We first define the reachability predicate between two individual locations *)
Reserved Notation "σ ⊨ l1 ⇝ l2" (at level 80, l1 at level 80, l2 at level 80).
Inductive reachability : Store -> Loc -> Loc ->Prop :=
| rch_heap: (**r we can access the current location *)
    forall l σ,
      l < dom σ ->
      σ ⊨ l ⇝ l
| rch_step: (**r we can access a location in the local environment of the object at l0 *)
    forall l0 l1 C f ω σ,
      l1 < dom σ ->
      getObj σ l0 = Some (C, ω) ->
      getVal ω f = Some l1 ->
      σ ⊨ l0 ⇝ l1
| rch_trans: (**r transitive case *)
    forall l0 l1 l2 σ,
      σ ⊨ l0 ⇝ l1 ->
      σ ⊨ l1 ⇝ l2 ->
      σ ⊨ l0 ⇝ l2
where "σ ⊨ l1 ⇝ l2" := (reachability σ l1 l2).

Global Hint Resolve rch_heap rch_step rch_trans: rch.
#[export] Hint Rewrite update_dom: rch.

(** We then extend the definition for a set of locations *)
Definition reachability_set σ (L: LocSet) l := exists l', (l' ∈ L) /\ (σ ⊨ l' ⇝ l).
Notation "σ ⊫ L ⇝ l" := (reachability_set σ L l) (at level 80, l at level 99, L at level 99).

(** Depending on the temperature of objects we can reach, we have three predicates about the store (plus the set version for each). Inside a store [σ], a location [l] is said to be:
- [reachable_cold]: if the location is in the heap (but might point to an object with unitialized fields)
- [reachable_warm]: if the location points to an object with all initialized fields (but those might point to cold objects)
- [reachable_hot]: if the location points to a hot object (transitively all initialized) *)
Definition reachable_cold (σ: Store) (l: Loc) := (l < dom σ).
Notation "σ ⊨ l : 'cold'" := (reachable_cold σ l) (at level 80, l at level 80).
Notation "σ ⊫ L : 'cold'" := (forall l, (l ∈ L) -> reachable_cold σ l) (at level 80, L at level 99).

Definition reachable_warm (σ: Store) (l: Loc) := (exists C ω args fields methods , (getObj σ l) = Some (C, ω) /\ ((ct C) = Some (class args fields methods)) /\ (length fields <= length ω)).
Notation "σ ⊨ l : 'warm'" := (reachable_warm σ l) (at level 80, l at level 80).
Notation "σ ⊫ L : 'warm'" := (forall l, (l ∈ L) -> reachable_warm σ l) (at level 80, L at level 99).

Definition reachable_hot  (σ: Store) (l: Loc) :=(forall (l': Loc), (σ ⊨ l ⇝ l') -> (σ ⊨ l' : warm)).
Notation "σ ⊨ l : 'hot'"  := (reachable_hot σ l) (at level 80, l at level 80).
Notation "σ ⊫ L : 'hot'" := (forall l, (l ∈ L) -> reachable_hot σ l) (at level 80, L at level 99).

(** A usefull rewrite *)
Ltac rch_singleton:=
  repeat match goal with
  | H: ?s ⊫ (Singleton Loc ?l1) ⇝ ?l2 |- _ =>
    let freshH := fresh "H" in
    unfold reachability_set in H;
    destruct H as [l' [freshH H] ]; induction freshH
  end.


(** *** Basic results *)
(** Rechable locations from a hot location lead to other hot locations *)
Lemma reachability_hot:
  forall σ l l',
    (σ ⊨ l: hot) ->
    σ ⊨ l ⇝ l' ->
    σ ⊨ l': hot.
Proof.
  unfold reachable_hot; eauto with rch.
Qed.

(** Reaching from a singleton is the same as reaching from the only element of the singleton *)
Lemma reachability_singleton :
  forall σ l1 l2,
    (σ ⊫ (Singleton Loc l1) ⇝ l2) <-> σ ⊨ l1 ⇝ l2.
Proof.
  split; intros; [rch_singleton | exists l1]; eauto => //.
Qed.

(* Reachable objects are inside the store *)
Lemma reachability_dom :
  forall σ l1 l2,
    (σ ⊨ l1 ⇝ l2) ->
    (l2 < (dom σ)).
Proof.
  intros.
  induction H;
    repeat steps || eapply_anywhere getObj_dom.
Qed.
Global Hint Resolve reachability_dom: rch.

(* Reachable objects are inside the store *)
Lemma reachability_dom2 :
  forall σ l1 l2,
    (σ ⊨ l1 ⇝ l2) ->
    (l1 < (dom σ)).
Proof.
  intros.
  induction H;
    repeat steps || eapply_anywhere getObj_dom.
Qed.
Global Hint Resolve reachability_dom2: rch.

(** We define a custom induction predicate. If a transitive property is true along heap paths, then it is true between any two reachable locations. *)
Lemma reachability_rev_ind:
  forall (P: Loc -> Loc -> Prop) σ,
    (forall l, l < dom σ -> P l l) -> (**r Heap case *)
    (forall l1 l2 l3, P l1 l2 -> P l2 l3 -> P l1 l3) -> (**r Transitive case *)
    (forall l l' C ω f , l' < dom σ -> getObj σ l = Some(C, ω) /\ getVal ω f = Some l' -> P l l') -> (**r Hop case *)
    (forall l l', σ ⊨ l ⇝ l' -> P l l').
Proof.
  intros.
  induction H2; eauto.
Qed.

(** When we ad a new location inside a local environment of an object, any new paths were either already in the previous store, or go through the added location *)
Lemma reachability_add_env:
  forall σ x C ω l,
    x < dom σ ->
    getObj σ x = Some(C, ω) ->
    forall l1 l2,
      ([x ↦ (C, ω ++ [l])]σ) ⊨ l1 ⇝ l2 ->
      σ ⊨ l1 ⇝ l2 \/ ((σ ⊨ l1 ⇝ x) /\ σ ⊨ l ⇝ l2).
Proof.
  intros σ x C ω l Hx Hobj.
  apply reachability_rev_ind; steps; eauto with rch;
    rewrite_anywhere update_dom; eauto with rch.
  eapply_anywhere getObj_update3; steps; eauto with rch.
  eapply_anywhere getVal_add; steps; eauto with rch.
Qed.

(** ** Notions of path into the heap *)

(** We define an existential predicate corresponding to the [rch_step] case *)
Definition reachable_one_step σ l0 l1 :=
  exists C ω f, getObj σ l0 = Some (C, ω) /\
           getVal ω f = Some l1 /\
           l1 < dom σ.

Lemma reachable_one_step_reachability :
  forall σ l0 l1, reachable_one_step σ l0 l1 -> σ ⊨ l0 ⇝ l1.
Proof.
  unfold reachable_one_step; steps.
  eauto with rch.
Qed.
Global Hint Resolve reachable_one_step_reachability : rch.

(** We define the notion of [reachable_path] in σ. The list of points are in reverse order (the head of the list is the end of the path) *)
Fixpoint reachable_path σ p {struct p}:=
  match p with
  | [] => True
  | l1::nil => l1 < dom σ
  | l2::((l1::_) as p') => reachable_one_step σ l1 l2 /\ reachable_path σ p'
  end.

(** A key notion for scopability proofs is to know if a path contains a given edge *)
Definition contains_edge p (l1 l2 :Loc) :=
  exists p1 p2, p = p2 ++ l2::l1::p1.

(** *** Basic properties of paths *)
(** Transitivity: *)
Lemma reachable_path_trans:
  forall σ p1 p2 l,
    reachable_path σ (p1++[l]) ->
    reachable_path σ (l::p2) ->
    reachable_path σ (p1++(l::p2)).
Proof.
  induction p1; [steps | intros].
  simpl in H |- *.
  repeat (destruct_match; [destruct p1; steps |]).
  assert (n0 = n) by (destruct p1; steps); subst.
  destruct_and.
  split; eauto.
  rewrite_back_any.
  eapply IHp1; eauto; steps.
Qed.

(** All elements along a path are reachable from the start: *)
Lemma reachable_path_is_reachable:
  forall σ p e l,
    reachable_path σ (e::p) ->
    List.In l (e::p) ->
    σ ⊨ l ⇝ e.
Proof.
  induction p ; try solve [repeat light ; eauto using rch_heap].
  intros.
  destruct H0 as [H0 | H0]; subst.
  + destruct p eqn:P ; repeat light;
      apply reachable_one_step_reachability, reachability_dom in H0;
      apply rch_heap; steps.
  + destruct p eqn:P; [steps; eauto with rch|].
    rewrite <- P in *. simpl in H.
    destruct_and.
    unfold reachable_one_step in H.
    flatten.
    eapply rch_trans with a; eauto with rch => //.
    eapply IHp => //.
Qed.

(** The last element in the path is also reachable: *)
Lemma reachable_path_last:
  forall σ s1 s2 p,
    reachable_path σ (p++[s2;s1]) ->
    reachable_path σ (p++[s2]).
Proof.
  induction p; simpl in *.
  + unfold reachable_one_step in * ; steps.
  + repeat (destruct_match; [ apply_anywhere app_eq_nil; steps | ]).
    assert ( n = n0) by (destruct p; steps); steps.
Qed.

(** Concatenation of paths: *)
Lemma reachable_path_app:
  forall σ s1 s2 p1 p2,
    reachable_path σ (p2++s2::p1++[s1]) ->
    reachable_path σ (s2::p1++[s1]) /\ reachable_path σ (p2++[s2]).
Proof.
  split.
  + move: H. move: s1 s2 p1.
    induction p2; simpl.
    ++ destruct p1; steps.
    ++ intros. repeat ( destruct_match; [apply_anywhere app_eq_nil; steps |]).
       repeat rewrite_back_any.
       steps; eapply_anywhere IHp2; steps.
  + assert (forall l p s, reachable_path σ (p++s::l) -> reachable_path σ (p++[s])); eauto.
    induction l; steps.
    specialize (IHl (p++[s]) a).
    eapply reachable_path_last.
    repeat rewrite <- app_assoc in *.
    simpl in *; eauto.
Qed.

(** **** Technical lemma :*)
Lemma app_exists_last:
  forall p (x:Loc),
  exists y p', x::p = p'++[y].
Proof.
  induction p; steps.
  + exists x, []; steps.
  + move /(_ a):IHp => IHp. steps.
    exists y, (x::p'); steps.
Qed.

(** *** Main equivalence result *)
Lemma reachable_path_reachability:
  forall σ s e,
    ((s = e /\ s < dom σ) \/ (**r trivial case *)
     exists p, reachable_path σ (e :: (p++[s]))) <-> σ ⊨ s ⇝ e. (**r main case if e ≠ s *)
Proof.
  split.
  + intros [[Heq Hdom] | [p Hp]]; subst; eauto with rch.
    generalize dependent e.
    induction p;
      repeat light;
      eauto with rch.
  + induction 1; flatten; eauto; right.
    ++ exists []; simpl; unfold reachable_one_step.
       repeat eexists; eauto using getObj_dom.
    ++ exists (p++(l1::p0)).
       rewrite <- app_assoc, app_comm_cons.
       eauto using reachable_path_trans, app_comm_cons.
Qed.

(** *** Other results *)
(** Splitting of paths: *)
Lemma reachable_path_app2:
  forall σ s p1 p2,
    reachable_path σ (p2++s::p1) ->
    reachable_path σ (p2++[s]).
Proof.
  assert (
      forall σ s s' p1 p2,
        reachable_path σ (p2 ++ s :: p1++[s']) ->
        reachable_path σ (p2 ++ [s])
    ) by repeat steps || eapply_anywhere reachable_path_app.
  intros; destruct p1 => //.
  pose proof (app_exists_last p1 n) ; steps.
  rewrite H1 in H0; eauto.
Qed.

(** Containing a given edge is decidable: *)
Lemma contains_edge_dec :
  forall p l1 l2,
    contains_edge p l1 l2 \/
    not (contains_edge p l1 l2).
Proof.
  unfold contains_edge. intros.
  induction p; steps.
  + right. steps. symmetry in H. apply app_eq_nil in H. steps.
  + left. exists p1, (a::p2); steps.
  + destruct_eq (a = l2); subst.
    ++ (**r a = l2 *)
      destruct p; steps.
      +++ right; steps. symmetry in H0. apply app_eq_unit in H0; steps.
      +++ destruct_eq (l = l1);
            [ left | right ]; steps;
              [ exists p, [] | destruct p2] ;
              steps; eauto.
    ++ (**r a ≠ l2 *)
      right; steps.
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

(** Combining previous results, we know that if a path contains a given edge [(l1,l2)], then [l1] is reachable from the start: *)
Lemma reachable_path_split_on_edge:
  forall σ s p l1 l2,
    reachable_path σ (p++[s]) ->
    contains_edge p l1 l2 ->
    σ ⊨ s ⇝ l1.
Proof.
  unfold contains_edge; steps.
  move: H. move: l1 l2 p1.
  induction p2; intros; simpl in *.
  + eapply reachable_path_is_reachable; flatten; eauto.
    rewrite app_comm_cons. apply in_app_iff; steps.
  + destruct_match; [apply_anywhere app_eq_nil; steps |].
    rewrite <- matched in *. flatten; eauto.
Qed.

(** When the local environment associated with an object is updated, if the updated value was not part of a given path in the updated store, then it was already valid in the un-updated store.  *)
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
  destruct p as [| l1 p]; [ simpl in *; subst; rewrite_anywhere update_one3; eauto |].
  simpl in H3. destruct_and.
  split.
  + unfold reachable_one_step in *; flatten.
    repeat rewrite_anywhere update_dom.
    destruct_eq (l1 = l); subst.
    ++ rewrite_anywhere getObj_update1; eauto using getObj_dom.
       invert_constructor_equalities; subst.
       destruct_eq (l2 = l'); subst ;
         [exfalso; apply H2; exists p, []  ; steps |].
       unfold getVal in *.
       exists C0, ω; repeat split; eauto.
       destruct_eq (f = f0); subst;
         rewrite_anywhere  update_one2; eauto.
       apply_anywhere update_one4; subst. congruence.
    ++ rewrite_anywhere getObj_update2; eauto using getObj_dom.
       repeat eexists || split || eauto.
  + apply IHp; eauto.
    intros [p1 [p2 Hedge]].
    apply H2. exists p1, (l2::p2).
    rewrite Hedge; eauto.
Qed.

(** A path in an updated store either goes through the new value or was already valid in the un-updated store*)
Lemma reachable_path_assignment :
  forall σ σ' C ω ω' p f l l',
    (getObj σ l) = Some (C, ω) ->
    ω' = [f ↦ l']ω ->
    σ' = [l ↦ (C, ω')]σ ->
    reachable_path σ' p ->
    contains_edge p l l' \/ reachable_path σ p.
Proof.
  intros.
  destruct (contains_edge_dec p l l') as [Hedge | Hedge]; eauto.
  right.
  induction p; eauto.
  simpl in *.
  destruct_match; [steps ; rewrite_anywhere update_one3 => // |].
  subst. flatten. intuition auto.
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
       +++ erewrite_anywhere update_one3; eauto.
    ++ rewrite_anywhere getObj_update2; eauto using getObj_dom.
       repeat eexists || eassumption.
       erewrite <- update_one3; eauto.
  + apply H2; clear H2.
    unfold reachable_one_step, contains_edge in *.
    intros. flatten.
    apply Hedge. exists p1, (a::p2). rewrite H2.
    rewrite app_comm_cons => //.
Qed.

(** A path is either trivial or contains a first step: *)
Lemma reachability_first_step:
  forall σ l1 l2,
    σ ⊨ l1 ⇝ l2 ->
    l1 = l2 \/ exists l0, reachable_one_step σ l1 l0.
Proof.
  unfold reachable_one_step.
  intros.
  induction H; steps.
  right.  repeat eexists; eauto.
Qed.

(** We can extract the last edge [(l,l')] of a path: *)
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

(** When adding a empty object, no path can go through it: *)
Lemma reachability_not_empty:
  forall σ C l, l < dom σ -> (σ++[(C, [])]) ⊨ (length σ) ⇝ l -> False .
Proof.
  intros.
  apply reachability_first_step in H0; steps; try lia.
  unfold reachable_one_step in *; steps.
  rewrite_anywhere getObj_last; invert_constructor_equalities; destruct f; steps.
Qed.

(** Extension of the previous result: a path in a store with a new empty object already existed in the store without it: *)
Lemma reachability_empty:
  forall σ C L l, l < dom σ ->((σ++[(C, [])]) ⊫ L ⇝ l) -> (σ ⊫ L ⇝ l).
Proof.
  intros.
  inversion H0 as [l1 [Hl1 Hrch]].
  exists l1; split => //.
  apply reachable_path_reachability in Hrch as [Hrch | [p Hrch]].
  + steps; eauto with rch.
  + clear Hl1 H0. generalize dependent l. generalize dependent l1.
    induction p; intros.
    ++ steps; unfold reachable_one_step in *; steps.
       repeat rewrite_anywhere dom_app.
       eapply getObj_last_empty in H2; eauto; steps.
       eapply rch_trans with l1; eauto using getObj_dom with rch.
    ++ move: (app_cons_not_nil p nil l1) => Hp.
       simpl in Hrch. destruct (p ++ [l1]) eqn:P; [exfalso; eauto |]. light.
       unfold reachable_one_step in H0.
       move: H0 => [C' [ω' [f [Hobja [ Hval Hdom]]]]] .
       pose proof (getObj_last_empty _ _ _ _ _ _ _ Hobja Hval) as [Hobj Hl1].
       light. eauto with rch.
Qed.

(** *** Technical results *)
Lemma reachability_weaken_assignment :
(** We define an existential predicate corresponding to the [rch_step] case *)
  forall σ σ' C ω ω' s e f l l',
    (getObj σ l) = Some (C, ω) ->
    ω' = [f ↦ l']ω ->
    σ' = [l ↦ (C, ω')]σ ->
    (l = l') ->
    σ' ⊨ s ⇝ e ->
    σ ⊨ s ⇝ e.
Proof.
  intros. move: H3. move: s e. induction 1; repeat steps || rewrite_anywhere update_dom; eauto with rch.
  eapply_anywhere getObj_update3; eauto using getObj_dom; steps; eauto with rch.
  eapply_anywhere getVal_update; steps;  eauto with rch.
Qed.

Lemma contains_edge_split:
  forall y x p p1 p2 (l l': Loc),
    y :: p ++ [x] = p1 ++ l' :: l :: p2 ->
    l' = y \/
    exists p1', p1 = y::p1' /\ y::p++[x] = y::p1'++l'::l::p2.
Proof.
  intros.
  destruct p1; steps.
  right.
  exists p1; rewrite_any; steps.
Qed.


Lemma contains_edge_last:
  forall l l' l0 p1',
    l <> l' ->
    contains_edge ((l0 :: p1') ++ [l']) l l' ->
    contains_edge (l0 :: p1') l l'.
Proof.
  unfold contains_edge; steps.
  destruct p1.
  - exfalso; eapply_any.
      eapply (app_inj_tail (p2 ++[l']) (l0::p1')).
      rewrite app_assoc_reverse; steps.
  - pose proof (app_exists_last p1 l1); flatten.
    rewrite H1 in H0.
    assert (l' = y). {
      eapply (app_inj_tail (l0::p1') (p2++l'::l::p'));
        rewrite app_assoc_reverse; eauto. }
    exists p', p2; steps.
    eapply app_inv_tail with [y].
    rewrite app_assoc_reverse; eauto.
Qed.
