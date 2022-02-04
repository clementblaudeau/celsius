(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the notion of reachability of a location in a given store. The set of reachable locations, starting from a given one l is transitively defined as the ones that can be accessed by following pointers in object local environments. We then define and prove basic properties around this notion. In the second part, we show the equivalence between the inductive definition and a path-based definition. This allows us to reason about paths from one location to another, especially for scopability results.  *)
From Celsius Require Export Language Helpers Notations.
Require Import ssreflect ssrbool Coq.Arith.Wf_nat Coq.Wellfounded.Wellfounded List Psatz Ensembles.
Import ListNotations.
Open Scope list_scope.


(** ** Definitions and notations *)
(** We first define the reachability predicate between two individual locations *)
Inductive reachability : Store -> Loc -> Loc -> Prop :=
| rch_heap: (**r we can access the current location *)
    forall l σ,
      l < dom σ ->
      reachability σ l l
| rch_step: (**r we can access a location in the local environment of the object at l0 *)
    forall l0 l1 C f ω σ,
      l1 < dom σ ->
      getObj σ l0 = Some (C, ω) ->
      getVal ω f = Some l1 ->
      reachability σ l0 l1
| rch_trans: (**r transitive case *)
    forall l0 l1 l2 σ,
      reachability σ l0 l1 ->
      reachability σ l1 l2 ->
      reachability σ l0 l2.

Global Instance notation_reachability : notation_dash_arrow Store Loc Loc :=
  { dash_arrow_ := reachability }.
Global Hint Unfold notation_reachability: notations.


Lemma rch_heap_n : forall (l: Loc) (σ: Store), l < dom σ -> σ ⊨ l ⇝ l.
Proof.
  autounfold with notations. eauto using reachability.
Qed.
Lemma rch_step_n : forall (l0 l1 : Loc) C f ω σ,
    l1 < dom σ ->
    getObj σ l0 = Some (C, ω) ->
    getVal ω f = Some l1 ->
    σ ⊨ l0 ⇝ l1.
Proof.
  autounfold with notations. eauto using reachability.
Qed.
Lemma rch_trans_n : forall (l0 l1 l2: Loc) σ,
    σ ⊨ l0 ⇝ l1 ->
    σ ⊨ l1 ⇝ l2 ->
    σ ⊨ l0 ⇝ l2.
Proof.
  autounfold with notations. eauto using reachability.
Qed.
Global Hint Resolve rch_heap_n rch_step_n rch_trans_n : rch.


Definition reachability_set σ (L: LocSet) l := exists l', (l' ∈ L) /\ (σ ⊨ l' ⇝ l).
Global Instance notation_reachability_set : notation_dash_arrow Store LocSet Loc :=
  { dash_arrow_ := reachability_set }.
Notation "σ ⊨ { l } ⇝ l'" := (reachability_set σ {l} l')  (at level 60, l at level 98, l' at level 98).
Global Hint Unfold notation_reachability_set: notations.

(** Depending on the temperature of objects we can reach, we have three predicates about the store. Inside a store [σ], a location [l] is said to be:
- [reachable_cold]: if the location is in the heap (but might point to an object with unitialized fields)
- [reachable_warm]: if the location points to an object with all initialized fields (but those might point to cold objects)
- [reachable_hot]: if the location points to a hot object (transitively all initialized) *)
Definition reachable_cold (σ: Store) (l: Loc) :=
  (l < dom σ).

Definition reachable_warm (σ: Store) (l: Loc) :=
  (exists C ω Args Flds Mtds ,
      (getObj σ l) = Some (C, ω) /\
        (ct C = (class Args Flds Mtds)) /\
        (length Flds <= length ω)).

Definition reachable_cool (σ: Store) (l: Loc) Ω :=
  exists C ω Args Flds Mtds ,
    getObj σ l = Some (C, ω) /\
      ct C = (class Args Flds Mtds) /\
      Ω <= dom ω.

Definition reachable_hot  (σ: Store) (l: Loc) :=
  forall (l': Loc),
    σ ⊨ l ⇝ l' ->
    reachable_warm σ l'.

Global Instance notation_reachability_mode : notation_dash_colon Store Loc Mode :=
  { dash_colon_ := fun σ l μ =>
                     match μ with
                     | cold => (reachable_cold σ l)
                     | warm => (reachable_warm σ l)
                     | hot => (reachable_hot σ l)
                     | cool Ω => reachable_cool σ l Ω
                     end
  }.
Global Instance notation_reachability_set_mode : notation_dash_colon Store LocSet Mode :=
  { dash_colon_ := fun σ L μ => forall l, l ∈ L -> σ ⊨ l : μ }.
Global Hint Unfold notation_reachability notation_reachability_set
       notation_reachability_mode notation_reachability_set_mode: notations.

(** ** Tactics *)

Ltac rch_singleton :=
  repeat match goal with
  | H: (reachability_set ?s (Singleton Loc ?l1) ?l2) |- _ =>
    let freshH := fresh "H" in
    unfold reachability_set in H;
    destruct H as [l' [freshH H] ]; induction freshH
  end.

Ltac rch_set :=
  repeat match goal with
         | H: ?σ ⊨ ?L ⇝ ?l |- _ =>
             let ln := fresh "l" in
             destruct H as [ln [H__ln H]]
         | H:_ |- _ ⊨ (Singleton Loc ?l) ⇝ _ =>
             exists l; split; [apply In_singleton |]
         end || inSingleton.

Global Hint Extern 1 => updates: rch.

(** *** Basic results *)
(** Rechable locations from a hot location lead to other hot locations *)
Lemma reachability_hot:
  forall σ (l l': Loc),
    σ ⊨ l : hot ->
    σ ⊨ l ⇝ l' ->
    σ ⊨ l': hot.
Proof.
  autounfold with notations.
  unfold reachable_hot; eauto with rch.
Qed.

(** Reaching from a singleton is the same as reaching from the only element of the singleton *)
Lemma reachability_singleton :
  forall σ l1 l2,
    (σ ⊨ {l1} ⇝ l2) <-> σ ⊨ l1 ⇝ l2.
Proof.
  split; intros; [rch_singleton | exists l1]; eauto => //.
Qed.

(* Reachable objects are inside the store *)
Lemma reachability_dom :
  forall σ (l1 l2: Loc),
    σ ⊨ l1 ⇝ l2 ->
    l2 < dom σ.
Proof.
  intros.
  induction H; steps.
Qed.
Global Hint Resolve reachability_dom: rch.

(* Reachable objects are inside the store *)
Lemma reachability_dom2 :
  forall σ (l1 l2: Loc),
    σ ⊨ l1 ⇝ l2 ->
    l1 < dom σ.
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
  forall σ x C ω (l: Loc),
    x < dom σ ->
    getObj σ x = Some(C, ω) ->
    forall (l1 l2: Loc),
      ([x ↦ (C, ω ++ [l])]σ) ⊨ l1 ⇝ l2 ->
      (σ ⊨ l1 ⇝ l2) \/ ((σ ⊨ l1 ⇝ x) /\ σ ⊨ l ⇝ l2).
Proof with eauto with rch notations.
  intros σ x C ω l Hx Hobj.
  apply reachability_rev_ind; steps;
    updates;
    eauto with rch notations.
  destruct_eq (x = l0); subst; updates...
  eapply_anywhere getVal_add; steps...
Qed.

(** ** Notions of path into the heap *)

(** We define an existential predicate corresponding to the [rch_step] case *)
Definition reachable_one_step σ (l0 l1: Loc) :=
  exists C ω f, getObj σ l0 = (Some (C, ω) : option Obj) /\
           getVal ω f = Some l1 /\
           l1 < dom σ.

Lemma reachable_one_step_reachability :
  forall σ l0 l1, reachable_one_step σ l0 l1 -> σ ⊨ l0 ⇝ l1.
Proof.
  unfold reachable_one_step; steps.
  eauto with rch notations.
Qed.
Global Hint Resolve reachable_one_step_reachability : rch.
Global Hint Extern 1 => eapply_anywhere reachable_one_step_reachability : rch.

(** We define the notion of [reachable_path] in σ. The list of points are in reverse order (the head of the list is the end of the path) *)
Fixpoint reachable_path σ (p: list Loc) {struct p}:=
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
  assert (l0 = l2) by (destruct p1; steps); subst.
  destruct_and.
  split; eauto.
  rewrite_back_any.
  eapply IHp1; eauto; steps.
Qed.

(** All elements along a path are reachable from the start: *)
Lemma reachable_path_is_reachable:
  forall (σ: Store) p e l,
    reachable_path σ (e::p) ->
    List.In l (e::p) ->
    σ ⊨ l ⇝ e.
Proof.
  induction p ; try solve [repeat light ; eauto using rch_heap with notations].
  intros.
  destruct H0 as [H0 | H0]; subst.
  + destruct p eqn:P ; repeat light;
      apply reachable_one_step_reachability, reachability_dom in H0;
      apply rch_heap; steps.
  + destruct p eqn:P; [steps; eapply reachable_one_step_reachability; eauto | ].
    rewrite <- P in *. simpl in *.
    destruct_and. eauto with rch.
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
    assert ( l = l1 ) by (destruct p; steps); steps.
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
  + exists x, ([]:list Loc); steps.
  + move /(_ a):IHp => IHp. steps.
    exists y, (x::p'); steps.
Qed.

(** *** Main equivalence result *)
Lemma reachable_path_reachability:
  forall σ (s e: Loc),
    ((s = e /\ s < dom σ) \/ (**r trivial case *)
     exists p, reachable_path σ (e :: (p++[s]))) <-> σ ⊨ s ⇝ e. (**r main case if e ≠ s *)
Proof.
  split.
  + intros [[Heq Hdom] | [p Hp]]; subst; eauto with rch notations.
    generalize dependent e.
    induction p;
      repeat light;
      eauto with rch notations.
  + induction 1; flatten; eauto; right.
    ++ eexists []; simpl; unfold reachable_one_step.
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
  pose proof (app_exists_last p1 l) ; steps.
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
              [ eexists p, [] | destruct p2] ;
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
Proof with (eauto with rch lia).
  intros.
  generalize dependent p.
  induction p as [| l2 p]; intros; simpl; eauto.
  destruct p as [| l1 p]; [ simpl in *; subst; updates; eauto |].
  simpl in H3. destruct_and.
  split.
  + unfold reachable_one_step in *; flatten; updates.
    destruct_eq (l = l1); subst; updates.
    ++ destruct_eq (l2 = l'); subst ;
         [exfalso; apply H2; eexists p, []  ; steps |].
       exists C0, ω; repeat split; eauto.
       destruct_eq (f = f0); subst; updates...
    ++ repeat eexists...
  + apply IHp; eauto.
    intros [p1 [p2 Hedge]].
    apply H2. exists p1, (l2::p2).
    rewrite Hedge; eauto.
Qed.

(** A path in an updated store either goes through the new value or was already valid in the un-updated store*)
Lemma reachable_path_assignment :
  forall (σ σ': Store) C ω ω' p (f l l' : Loc),
    (getObj σ l) = Some (C, ω) ->
    ω' = [f ↦ l']ω ->
    σ' = [l ↦ (C, ω')]σ ->
    reachable_path σ' p ->
    contains_edge p l l' \/ reachable_path σ p.
Proof with (updates; eauto with rch lia).
  intros.
  destruct (contains_edge_dec p l l') as [Hedge | Hedge]; eauto.
  right.
  induction p as [| n p ]; eauto.
  simpl in *.
  subst.
  destruct_match... intuition auto.
  - clear H2. clear H1. unfold reachable_one_step in *; steps...
    pose proof (getObj_dom _ _ _ H1)...
    destruct (getObj_Some σ l0 H2) as (C' & ω' & H__getObj).
    exists C', ω'.
    destruct_eq (l = l0); subst; updates; cross_rewrites.
    + destruct_eq (f = f0); subst; updates.
      * exfalso. apply Hedge.
           unfold contains_edge.
           exists l1, ([]: list Loc); steps.
      * exists f0; splits...
    + exists f0; splits...
  - apply H2; clear H2.
    unfold reachable_one_step, contains_edge in *.
    intros. flatten.
    apply Hedge. exists p1, (n::p2). rewrite H2.
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

(** *** Technical results *)
Lemma reachability_weaken_assignment :
(** We define an existential predicate corresponding to the [rch_step] case *)
  forall (σ σ':Store) C ω ω' (s e: Loc) f l l',
    (getObj σ l) = Some (C, ω) ->
    ω' = [f ↦ l']ω ->
    σ' = [l ↦ (C, ω')]σ ->
    (l = l') ->
    σ' ⊨ s ⇝ e ->
    σ ⊨ s ⇝ e.
Proof with (updates; eauto with rch lia).
  intros. move: H3. move: s e.
  induction 1; subst...
  destruct_eq (l' = l0); subst ...
  destruct_eq (f = f0); subst ...
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


(** Decidability of reachability *)
Section rch_decidability.

  Inductive reachability_trace : Store -> Loc -> Loc -> (list Loc) -> Prop :=
  | rch_t_heap : forall σ l,
      l < dom σ ->
      reachability_trace σ l l []
  | rch_t_step : forall σ l C ω f l',
      getObj σ l = Some (C, ω) ->
      getVal ω f = Some l' ->
      l' < dom σ ->
      reachability_trace σ l l' []
  | rch_t_trans : forall σ l0 l1 l2 t1 t2,
      reachability_trace σ l0 l1 t1 ->
      reachability_trace σ l1 l2 t2 ->
      reachability_trace σ l0 l2 (t1++l1::t2).
  Local Hint Constructors reachability_trace: rch_t.

  Lemma reachability_trace_reachability:
    forall σ l l',
      (σ ⊨ l ⇝ l') <-> (exists p, reachability_trace σ l l' p).
  Proof with (eauto with rch rch_t).
    split; intros.
    - induction H...
      destruct IHreachability1 as [p1 IH1].
      destruct IHreachability2 as [p2 IH2].
      exists (p1++(l1::p2))...
    - destruct H as [p H].
      induction H...
  Qed.
  Local Hint Resolve reachability_trace_reachability: rch_t.

  Lemma reachability_trace_reachability_reverse:
    forall σ l l' p,
      reachability_trace σ l l' p -> (σ ⊨ l ⇝ l').
  Proof.
    intros.
    apply reachability_trace_reachability; eauto.
  Qed.
  Local Hint Resolve reachability_trace_reachability_reverse: rch_t.

  Lemma reachability_trace_is_reachable:
    forall σ l l' tr l__m,
      (reachability_trace σ l l' tr /\
         List.In l__m tr) <->
        (exists t0 t1, tr = t0 ++ l__m :: t1 /\
                    reachability_trace σ l l__m t0 /\
                    reachability_trace σ l__m l' t1).
  Proof with (eauto using app_assoc_reverse with rch_t rch).
    split; intros.
    - destruct H as [H ?].
      induction H; steps.
      apply in_app_iff in H0 as [|[|]].
      + lets (t & t' & ? & ? & ?): IHreachability_trace1 H0.
        exists t, (t'++l1::t2); subst; splits... rewrite app_assoc_reverse...
      + subst.
        exists t1, t2; splits...
      + lets (t & t' & ? & ? & ?): IHreachability_trace2 H0.
        exists (t1++l1::t), t'; subst; splits... rewrite app_assoc_reverse...
    - destruct H as (t0 & t1 & ? & ? & ?). subst.
      split...
      apply in_elt.
  Qed.

   Lemma reachability_trace_head_reachable:
    forall σ l l' tr l__m,
      reachability_trace σ l l' (l__m::tr) ->
      reachability_trace σ l l__m [] /\
        reachability_trace σ l__m l' tr.
  Proof with (eauto using app_assoc_reverse with rch_t rch).
    intros.
    remember (l__m::tr) as T. gen l__m tr.
    induction H; intros... steps. steps.
    destruct t1; steps...
  Qed.

  Lemma NoDup_app:
    forall [A: Type] (l l': list A),
      NoDup (l++l') -> NoDup l /\ NoDup l'.
  Proof with (eauto using NoDup).
    induction l; simpl; intros...
    inverts H...
    apply IHl in H3 as [ ]. split...
    apply NoDup_cons...
    intros Hf; apply H2, in_app_iff...
  Qed.

  Lemma reachability_trace_NoDup:
    forall σ l l' tr,
      reachability_trace σ l l' tr ->
      exists ntr, reachability_trace σ l l' ntr /\ NoDup ntr.
  Proof with (eauto using NoDup with rch_t).
    intros. gen l l'.
    induction tr; intros.
    - inverts H;
        exists ([]: list Loc); splits...
      exfalso. eapply app_cons_not_nil; eauto.
    - lets [ ]: reachability_trace_head_reachable H.
      lets (ntr & ? & ?): IHtr H1.
      destruct (in_dec (PeanoNat.Nat.eq_dec) a ntr).
      + clear IHtr H1 H.
        pose proof (proj1 (iff_and (reachability_trace_is_reachable σ a l' ntr a)))
          as (t0 & t1 & ? & ? & ?)...
        exists (a::t1); split.
        * replace (a::t1) with ([]++a::t1) by steps...
        * subst. eapply NoDup_app...
      + exists (a::ntr); split...
        replace (a::ntr) with ([]++a::ntr) by steps...
  Qed.


  Lemma split_or {X} (l : list X) (P Q : X -> Prop) :
    (forall x, List.In x l -> (P x \/ Q x)) ->
    (exists x, List.In x l /\ P x) \/ (forall x, List.In x l -> Q x).
  Proof.
    induction l; intros.
    + right; intros; inversion H0.
    + destruct (H a) as [HP | HQ]; [simpl; eauto | | ].
      ++ left; exists a; simpl; eauto.
      ++ destruct IHl as [[x0 [Hin HP]] | HQ2]; eauto.
         +++ intros y. specialize (H y).
             intros.
             apply H; simpl; eauto.
         +++ left. exists x0; split; simpl; eauto.
         +++ right; intros.
             destruct H0; subst; eauto.
  Qed.

  Lemma In_tail:
    forall (X: Type) (l1 l2: list X) x,
      (forall y, List.In y l1 -> List.In y (x::l2)) ->
      (List.In x l1) \/ (forall y, List.In y l1 -> List.In y l2).
  Proof.
    intros.
    pose proof (split_or l1 (fun y => x=y) (fun y => List.In y l2)).
    simpl in H0, H.
    apply H0 in H as [[y [H1 H2]] | H1]; subst; eauto.
  Qed.


  Theorem pigeonhole_principle:
    forall (X:Type) (l1 l2:list X),
      length l2 < length l1 ->
      (forall x, List.In x l1 -> List.In x l2) ->
      ~ NoDup l1.
  Proof.
    induction l1 as [|x l1 IH].
    - intros.
      inversion H.
    - intros.
      pose proof (H0 x) as H1; simpl; eauto.
      apply in_split in H1 as [l3 [l4 H1]]; simpl; eauto.
      specialize (IH (l3++l4)).
      subst.
      repeat rewrite app_length in H || simpl in H.
      repeat rewrite app_length in IH || simpl in IH.
      remember (l3++l4) as l2'.
      assert (forall y, List.In y l1 -> List.In y (x::l2')).
      + intros. subst.
        specialize (H0 y).
        simpl in *. steps.
        rewrite in_app_iff in H0.
        rewrite in_app_iff. steps.
      + intros HD. inverts HD.
        apply In_tail in H1 as [H1 | H1]; eauto using NoDup.
        apply IH; eauto with lia.
  Qed.

  Import PeanoNat.Nat.

  Fixpoint reachabilityb n σ l l' :=
    (eqb l l' && ltb l (dom σ))
    || match getObj σ l with
      | Some (C, ω) => existsb (eqb l') ω && ltb l' (dom σ)
      | None => false
      end
    || match n with
      | 0   => false
      | S n => existsb (fun l0 => (reachabilityb n σ l l0) && (reachabilityb n σ l0 l')) (seq 0 (dom σ))
      end.

  Lemma reachabilityb_monotonicity:
    forall n1 n2 σ l l',
      n1 <= n2 ->
      reachabilityb n1 σ l l' ->
      reachabilityb n2 σ l l'.
  Proof with (bools; eauto with lia).
    intros n1 n2. gen n1.
    induction n2; simpl in *; intros...
    - assert (n1 = 0) by lia; subst.
      simpl in H0...
    - apply Bool.orb_true_iff.
      destruct n1; simpl in *.
      + apply Bool.orb_true_iff in H0; steps.
      + apply Bool.orb_true_iff in H0 as [|]...
        right.
        apply existsb_exists in H0 as [x [? ?]].
        apply existsb_exists; exists x; splits...
        flatten.
        split; eapply IHn2 with (n1 := n1)...
  Qed.

  Lemma reachabilityb_reachability:
    forall n σ l l',
      reachabilityb n σ l l' = true -> σ ⊨ l ⇝ l'.
  Proof with (bools; eauto with rch lia).
    induction n; simpl; intros...
    - destruct H as [[[Heq Hlt]|]|]; try discriminate.
      + rewrite eqb_eq in Heq. subst.
        rewrite ltb_lt in Hlt...
      + destruct (getObj σ l) as [[C ω]|] eqn:?; [|discriminate]...
        destruct H as [Hex Hlt].
        apply existsb_exists in Hex as [x [ ]].
        rewrite eqb_eq in H0. subst.
        apply In_nth_error in H as [f ?].
        apply ltb_lt in Hlt.
        eapply rch_step...
    - destruct H as [[[Heq Hlt]|]|].
      + rewrite eqb_eq in Heq. subst.
        rewrite ltb_lt in Hlt...
      + destruct (getObj σ l) as [[C ω]|] eqn:?; [|discriminate]...
        destruct H as [Hex Hlt].
        apply existsb_exists in Hex as [x [ ]].
        rewrite eqb_eq in H0. subst.
        apply In_nth_error in H as [f ?].
        apply ltb_lt in Hlt.
        eapply rch_step...
      + apply existsb_exists in H as [l0 [H__l0 ?]].
        apply andb_prop in H as [ ].
        apply rch_trans_n with l0...
  Qed.
  Local Hint Resolve reachabilityb_reachability: rch_t.

  Lemma reachability_trace_reachabilityb:
    forall σ l l' tr,
      reachability_trace σ l l' tr -> reachabilityb (length tr) σ l l'.
  Proof with (bools; eauto with lia rch_t rch).
    intros.
    induction H; simpl...
    - apply Bool.orb_true_iff. left.
      apply Bool.orb_true_iff. left.
      apply andb_true_intro; split.
      rewrite eqb_eq...
      rewrite ltb_lt...
    - apply Bool.orb_true_iff. left.
      apply Bool.orb_true_iff. right.
      rewrite H.
      apply andb_true_intro; split.
      apply existsb_exists. exists l'; split.
      eapply nth_error_In, H0.
      rewrite eqb_eq...
      rewrite ltb_lt...
    - remember (dom t1) as n1.
      remember (dom t2) as n2.
      rewrite app_length; simpl.
      rewrite -Heqn1 -Heqn2 -plus_n_Sm. simpl.
      apply Bool.orb_true_intro. right.
      apply existsb_exists. exists l1. split; simpl.
      + apply in_seq; simpl; split...
      + apply andb_true_intro; split;
          eapply reachabilityb_monotonicity ; try eassumption...
  Qed.
  Local Hint Resolve reachability_trace_reachabilityb : rch_t.

  Implicit Type l : Loc.
  Theorem reachability_dec:
    forall σ l l',
      {σ ⊨ l ⇝ l'} + {~ σ ⊨ l ⇝ l'}.
  Proof with (eauto with rch rch_t lia).
    intros.
    assert (reflect (σ ⊨ l ⇝ l') (reachabilityb (dom σ) σ l l')); [| inverts H; eauto].
    assert ((σ ⊨ l ⇝ l') <-> exists tr, reachability_trace σ l l' tr /\ (length tr <= dom σ)).
    - split; intros.
      + apply reachability_trace_reachability in H as [tr0 H].
        apply reachability_trace_NoDup in H as [tr [H Hdup]].
        exists tr; split...
        assert (dom σ < dom tr \/ dom tr <= dom σ) as [|] by lia...
        assert (dom σ = dom (seq 0 (dom σ))); try rewrite seq_length...
        rewrite H1 in H0.
        eapply pigeonhole_principle in H0. exfalso...
        intros. apply in_seq; simpl; split...
        pose proof (reachability_trace_is_reachable σ l l' tr x) as [(t0 & t1 & ? & ? & _) _]...
      + destruct H as [tr [ ]]...
    - destruct (reachabilityb (dom σ) σ l l') eqn:Hb.
      + apply Bool.ReflectT...
      + apply Bool.ReflectF.
        intros Hf. apply H in Hf as [tr [Hf Htr]].
        apply reachability_trace_reachabilityb, reachabilityb_monotonicity with (n2 := dom σ) in Hf...
  Qed.

End rch_decidability.

Check reachability_dec.
