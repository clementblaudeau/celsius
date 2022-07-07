(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL & Inria 2020-2022 *)
(* ------------------------------------------------------------------------ *)
(* This file defines the notion of reachability of a location in a given store. The set of reachable
locations, starting from a given one l is transitively defined as the ones that can be accessed by
following pointers in object local environments. We then define and prove basic properties around
this notion. At the end, the Reachability_dec section shows that the predicate is decidable *)

From Celsius Require Export Helpers.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc) (L: LocSet).

(* ------------------------------------------------------------------------ *)
(** ** Reachability *)
(* We first define the reachability predicate between two individual locations *)

Inductive reachability : Store -> Loc -> Loc -> Prop :=

(* we can access the current location *)
| rch_heap:
    forall l σ,
      l < dom σ ->
      reachability σ l l

(* we can access a location in the local environment of the object at l0 *)
| rch_step:
    forall l0 l1 C f ω σ,
      l1 < dom σ ->
      getObj σ l0 = Some (C, ω) ->
      getVal ω f = Some l1 ->
      reachability σ l0 l1

(* transitive case *)
| rch_trans:
    forall l0 l1 l2 σ,
      reachability σ l0 l1 ->
      reachability σ l1 l2 ->
      reachability σ l0 l2.

Global Hint Constructors reachability: rch.

(** We define the instance for the notation *)
Global Instance notation_reachability : notation_dash_arrow Store Loc Loc :=
  { dash_arrow_ := reachability }.
Global Hint Unfold dash_arrow_ notation_reachability: rch.

(* Then we define the reachability predicate for sets of locations *)
Definition reachability_set σ L l :=
  exists l', (l' ∈ L) /\ (σ ⊨ l' ⇝ l).

Global Instance notation_reachability_set : notation_dash_arrow Store LocSet Loc :=
  { dash_arrow_ := reachability_set }.
Notation "σ ⊨ { l } ⇝ l'" := (reachability_set σ {l} l')  (at level 60, l at level 98, l' at level 98).
Global Hint Unfold notation_reachability_set: rch.


(* ------------------------------------------------------------------------ *)
(** ** Semantic modes *)
(* We then define the modes (cold, cool, warm, hot) as predicates over the store (and a location):
- cold: the location is in the heap
- cool Ω: the object at l as at least Ω fields
- warm: the object has all fields initialized (regarding its definition)
- hot: the object can only reach warm objects *)

Inductive semantic_mode : Store -> Loc -> Mode -> Prop :=

| sm_cold: forall σ l, l < dom σ -> semantic_mode σ l cold

| sm_warm: forall σ l C ω Args Flds Mtds,
    getObj σ l = Some (C, ω) ->
    ct C = class Args Flds Mtds ->
    length Flds <= length ω ->
    semantic_mode σ l warm

| sm_cool: forall σ l Ω C ω Args Flds Mtds,
    getObj σ l = Some (C, ω) ->
    ct C = class Args Flds Mtds ->
    Ω <= dom ω ->
    semantic_mode σ l (cool Ω)

| sm_hot: forall σ l,
    (forall (l': Loc),
        σ ⊨ l ⇝ l' ->
        semantic_mode σ l' warm) ->
    semantic_mode σ l hot.

Global Hint Constructors semantic_mode: core.

Global Instance notation_semantic_mode : notation_dash_colon Store Loc Mode :=
  { dash_colon_ := semantic_mode}.
Global Instance notation_semantic_set_mode : notation_dash_colon Store LocSet Mode :=
  { dash_colon_ := fun σ L μ => forall l, l ∈ L -> σ ⊨ l : μ }.

Global Hint Unfold notation_semantic_mode notation_semantic_set_mode: rch.
Global Hint Extern 1 => (eapply sm_warm): rch.

(* ------------------------------------------------------------------------ *)
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

(* ------------------------------------------------------------------------ *)
(** ** Basic results *)
(* Rechable locations from a hot location lead to other hot locations *)

Lemma rch_hot_trans:
  forall σ l l',
    σ ⊨ l : hot ->
    σ ⊨ l ⇝ l' ->
    σ ⊨ l' : hot.
Proof.
  intros.
  apply sm_hot; intros.
  inverts H;
    eauto with rch.
Qed.

(** Reaching from a singleton is the same as reaching from the only element of the singleton *)
Lemma rch_singleton :
  forall σ l1 l2,
    (σ ⊨ {l1} ⇝ l2) <-> σ ⊨ l1 ⇝ l2.
Proof.
  split; intros; [rch_singleton | exists l1]; eauto => //.
Qed.

(* Reachable objects are inside the store *)
Lemma rch_dom :
  forall σ l1 l2,
    σ ⊨ l1 ⇝ l2 ->
    l2 < dom σ.
Proof.
  intros.
  induction H; steps.
Qed.
Global Hint Resolve rch_dom: rch.

Lemma rch_dom2 :
  forall σ l1 l2,
    σ ⊨ l1 ⇝ l2 ->
    l1 < dom σ.
Proof.
  intros.
  induction H;
    repeat steps || eapply_anywhere getObj_dom.
Qed.
Global Hint Resolve rch_dom2: rch.

(* Basic results about reachability and unions *)
Lemma rch_union_introl :
  forall σ L1 L2 l,
    σ ⊨ L1 ⇝ l ->
    σ ⊨ L1 ∪ L2 ⇝ l.
Proof.
  intros. destruct H as (l0 & ? & ?).
  exists l0; split; eauto using Union_introl.
Qed.

Lemma rch_union_intror :
  forall σ L1 L2 l,
    σ ⊨ L2 ⇝ l ->
    σ ⊨ L1 ∪ L2 ⇝ l.
Proof.
  intros. destruct H as (l0 & ? & ?).
  exists l0; split; eauto using Union_intror.
Qed.
Global Hint Resolve rch_union_introl rch_union_intror: rch.

(* ------------------------------------------------------------------------ *)
(** ** Reachability and assignments *)

(* When we *add a new location* inside a local environment of an object, any new paths were either
already in the previous store, or go through the added location *)

Lemma rch_asgn_new:
  forall σ l0 l1 C ω,
    getObj σ l0 = Some(C, ω) ->
    forall l l' σ',
      σ' ⊨ l ⇝ l' ->
      σ' = ([l0 ↦ (C, ω ++ [l1])]σ) ->
      (σ ⊨ l ⇝ l') \/ ((σ ⊨ l ⇝ l0) /\ (σ ⊨ l1 ⇝ l')).
Proof with eauto with rch notations.
  intros.
  induction H0; subst; updates...
  - destruct_eq (l0 = l2); subst; updates...
    apply getVal_add in H3; steps...
    right; split...
  - intuition auto...
    + right; split...
    + right; split...
Qed.

(* A path in an updated store either goes through the new value or was already valid in the
un-updated store*)

Lemma rch_asgn :
  forall σ C ω f l0 l1,
    getObj σ l0 = Some (C, ω) ->
    forall l l' σ',
      σ' ⊨ l ⇝ l' ->
      σ' = [l0 ↦ (C, [f ↦ l1] ω)] σ ->
      (σ ⊨ l ⇝ l') \/ ((σ ⊨ l ⇝ l0) /\ (σ ⊨ l1 ⇝ l')).
Proof with (eauto with rch).
  intros.
  induction H0; subst; updates...
  - destruct_eq (l0 = l2); subst; updates...
    destruct_eq (f = f0); subst; updates...
    right; split...
  - intuition auto...
    + right; split...
    + right; split...
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Decidability of reachability *)

Section Reachability_Dec.

  Reserved Notation "s ⊨ x ⇝ y ↑ tr" (at level 60, x at level 98, y at level 98, tr at level 98).
  Inductive reachability_trace : Store -> Loc -> Loc -> (list Loc) -> Prop :=
  | rch_t_heap : forall σ l,
      l < dom σ ->
      σ ⊨ l ⇝ l ↑ []
  | rch_t_step : forall σ l C ω f l',
      getObj σ l = Some (C, ω) ->
      getVal ω f = Some l' ->
      l' < dom σ ->
      σ ⊨ l ⇝ l' ↑ []
  | rch_t_trans : forall σ l0 l1 l2 t1 t2,
      σ ⊨ l0 ⇝ l1 ↑ t1 ->
      σ ⊨ l1 ⇝ l2 ↑ t2 ->
      σ ⊨ l0 ⇝ l2 ↑ (t1++l1::t2)
  where "s ⊨ x ⇝ y ↑ tr" := (reachability_trace s x y tr).
  Local Hint Constructors reachability_trace: rch.

  Lemma rch_iff_rch_tr:
    forall σ l l',
      (σ ⊨ l ⇝ l') <-> (exists tr, σ ⊨ l ⇝ l' ↑ tr).
  Proof with (eauto with rch).
    split; intros.
    - induction H; flatten; eexists...
    - destruct H as [tr H].
      induction H...
  Qed.
  Local Hint Resolve rch_iff_rch_tr: rch.

  Lemma rch_tr_implies_rch:
    forall σ l l' tr,
      σ ⊨ l ⇝ l' ↑ tr ->
      σ ⊨ l ⇝ l'.
  Proof with (eauto with rch).
    intros.
    eapply rch_iff_rch_tr...
  Qed.
  Local Hint Resolve rch_tr_implies_rch: rch.

  Lemma rch_tr_in_rch:
    forall σ l l' tr l__m,
      ((σ ⊨ l ⇝ l' ↑ tr) /\ (List.In l__m tr)) <->
        (exists t0 t1, tr = t0 ++ l__m :: t1 /\
                    (σ ⊨ l ⇝ l__m ↑ t0) /\
                    (σ ⊨ l__m ⇝ l' ↑ t1)).
  Proof with (eauto using app_assoc_reverse with rch).
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

  Lemma rch_tr_hd_rch:
    forall σ l l' tr l__m,
      (σ ⊨ l ⇝ l' ↑ (l__m::tr)) ->
      (σ ⊨ l ⇝ l__m ↑ []) /\
        (σ ⊨ l__m ⇝ l' ↑ tr).
  Proof with (eauto using app_assoc_reverse with rch).
    intros.
    remember (l__m::tr) as T. gen l__m tr.
    induction H; intros; steps;
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

  Lemma rch_tr_NoDup:
    forall σ l l' tr,
      σ ⊨ l ⇝ l' ↑ tr ->
      exists tr__nd, (σ ⊨ l ⇝ l' ↑ tr__nd) /\ NoDup tr__nd.
  Proof with (eauto using NoDup with rch).
    intros. gen l l'.
    induction tr; intros.
    - inverts H;
        exists ([]: list Loc); splits...
    - lets [ ]: rch_tr_hd_rch H.
      lets (tr__nd & ? & ?): IHtr H1.
      destruct (in_dec (PeanoNat.Nat.eq_dec) a tr__nd).
      + clear IHtr H1 H.
        pose proof (proj1 (iff_and (rch_tr_in_rch σ a l' tr__nd a)))
          as (t0 & t1 & ? & ? & ?)...
        exists (a::t1); split.
        * replace (a::t1) with ([]++a::t1) by steps...
        * subst. eapply NoDup_app...
      + exists (a::tr__nd); split...
        replace (a::tr__nd) with ([]++a::tr__nd) by steps...
  Qed.


  Lemma split_or {X} (l : list X) (P Q : X -> Prop) :
    (forall x, List.In x l -> (P x \/ Q x)) ->
    (exists x, List.In x l /\ P x) \/ (forall x, List.In x l -> Q x).
  Proof.
    induction l; intros.
    - right; intros; inversion H0.
    - destruct (H a) as [HP | HQ]; [simpl; eauto | | ].
      + left; exists a; simpl; eauto.
      + destruct IHl as [[x0 [Hin HP]] | HQ2]; eauto.
        * intros y. specialize (H y).
          intros.
          apply H; simpl; eauto.
        * left. exists x0; split; simpl; eauto.
        * right; intros.
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

  Fixpoint rchb n σ l l' :=
    (eqb l l' && ltb l (dom σ))
    || match getObj σ l with
      | Some (C, ω) => existsb (eqb l') ω && ltb l' (dom σ)
      | None => false
      end
    || match n with
      | 0   => false
      | S n => existsb (fun l0 => (rchb n σ l l0) && (rchb n σ l0 l')) (seq 0 (dom σ))
      end.

  Lemma rchb_monotonicity:
    forall n1 n2 σ l l',
      n1 <= n2 ->
      rchb n1 σ l l' ->
      rchb n2 σ l l'.
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

  Lemma rchb_reachability:
    forall n σ l l',
      rchb n σ l l' = true -> σ ⊨ l ⇝ l'.
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
        apply rch_trans with l0;
          apply IHn...
  Qed.
  Local Hint Resolve rchb_reachability: rch_t.

  Lemma rch_tr_rchb:
    forall σ l l' tr,
      σ ⊨ l ⇝ l' ↑ tr -> rchb (length tr) σ l l'.
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
          eapply rchb_monotonicity ; try eassumption...
  Qed.
  Local Hint Resolve rch_tr_rchb : rch_t.

  Theorem reachability_dec:
    forall σ l l',
      {σ ⊨ l ⇝ l'} + {~ σ ⊨ l ⇝ l'}.
  Proof with (eauto with rch rch_t lia).
    intros.
    assert (reflect (σ ⊨ l ⇝ l') (rchb (dom σ) σ l l')); [| inverts H; eauto].
    assert ((σ ⊨ l ⇝ l') <-> exists tr, (σ ⊨ l ⇝ l' ↑ tr) /\ (length tr <= dom σ)).
    - split; intros.
      + apply rch_iff_rch_tr in H as [tr0 H].
        apply rch_tr_NoDup in H as [tr [H Hdup]].
        exists tr; split...
        assert (dom σ < dom tr \/ dom tr <= dom σ) as [|] by lia...
        assert (dom σ = dom (seq 0 (dom σ))); try rewrite seq_length...
        rewrite H1 in H0.
        eapply pigeonhole_principle in H0. exfalso...
        intros. apply in_seq; simpl; split...
        pose proof (rch_tr_in_rch σ l l' tr x) as [(t0 & t1 & ? & ? & _) _]...
      + destruct H as [tr [ ]]...
    - destruct (rchb (dom σ) σ l l') eqn:Hb.
      + apply Bool.ReflectT...
      + apply Bool.ReflectF.
        intros Hf. apply H in Hf as [tr [Hf Htr]].
        apply rch_tr_rchb, rchb_monotonicity with (n2 := dom σ) in Hf...
  Qed.

End Reachability_Dec.
