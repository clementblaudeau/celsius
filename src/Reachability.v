(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the notion of reachability of a location in a given store. The set of reachable locations, starting from a given one l is transitively defined as the ones that can be accessed by following pointers in object local environments. We then define and prove basic properties around this notion. In the second part, we show the equivalence between the inductive definition and a path-based definition. This allows us to reason about paths from one location to another, especially for scopability results.  *)
From Celsius Require Export Language Helpers Notations.
Require Import ssreflect ssrbool Coq.Arith.Wf_nat Coq.Wellfounded.Wellfounded List Psatz Ensembles.
Import ListNotations.
Open Scope list_scope.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc) (L: LocSet).

(* TOCLEAN *)
Ltac app_eq_nil :=
  repeat match goal with
         | H: [] = _ ++ (_ :: _) |- _ => symmetry in H
         | H: _ ++ (_ :: _) = [] |- _ =>
             exfalso; apply app_eq_nil in H as [_ H];
             inverts H
         end.
Global Hint Extern 1 => app_eq_nil: core.


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
Global Hint Constructors reachability: rch.

(** We define the instance for the notation *)
Global Instance notation_reachability : notation_dash_arrow Store Loc Loc :=
  { dash_arrow_ := reachability }.
Global Hint Unfold dash_arrow_ notation_reachability: rch.

(** Then we define the reachability predicate for sets of locations *)
Definition reachability_set σ L l := exists l', (l' ∈ L) /\ (σ ⊨ l' ⇝ l).
Global Instance notation_reachability_set : notation_dash_arrow Store LocSet Loc :=
  { dash_arrow_ := reachability_set }.
Notation "σ ⊨ { l } ⇝ l'" := (reachability_set σ {l} l')  (at level 60, l at level 98, l' at level 98).
Global Hint Unfold notation_reachability_set: rch.

(** Depending on the temperature of objects we can reach, we have three predicates about the store. Inside a store [σ], a location [l] is said to be:
- [reachable_cold]: if the location is in the heap (but might point to an object with unitialized fields)
- [reachable_warm]: if the location points to an object with all initialized fields (but those might point to cold objects)
- [reachable_hot]: if the location points to a hot object (transitively all initialized) *)
Definition reachable_cold σ l :=
  (l < dom σ).

Definition reachable_warm σ l :=
  (exists C ω Args Flds Mtds ,
      (getObj σ l) = Some (C, ω) /\
        (ct C = (class Args Flds Mtds)) /\
        (length Flds <= length ω)).

Definition reachable_cool σ l Ω :=
  exists C ω Args Flds Mtds ,
    getObj σ l = Some (C, ω) /\
      ct C = (class Args Flds Mtds) /\
      Ω <= dom ω.

Definition reachable_hot σ l :=
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

Global Hint Unfold reachable_cold reachable_cool reachable_hot reachable_warm: rch.
Global Hint Unfold notation_reachability_mode notation_reachability_set_mode: rch.

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
  forall σ l l',
    σ ⊨ l : hot ->
    σ ⊨ l ⇝ l' ->
    σ ⊨ l': hot.
Proof.
  intros. cbn in *.
  unfold reachable_hot in *.
  eauto with rch.
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
  forall σ l1 l2,
    σ ⊨ l1 ⇝ l2 ->
    l2 < dom σ.
Proof.
  intros.
  induction H; steps.
Qed.
Global Hint Resolve reachability_dom: rch.

(* Reachable objects are inside the store *)
Lemma reachability_dom2 :
  forall σ l1 l2,
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
  forall σ x C ω l,
    x < dom σ ->
    getObj σ x = Some(C, ω) ->
    forall (l1 l2: Loc),
      ([x ↦ (C, ω ++ [l])]σ) ⊨ l1 ⇝ l2 ->
      (σ ⊨ l1 ⇝ l2) \/ ((σ ⊨ l1 ⇝ x) /\ σ ⊨ l ⇝ l2).
Proof with eauto with rch notations.
  intros σ x C ω l Hx Hobj.
  apply reachability_rev_ind; steps;
    updates; try solve [right; eauto with rch]...
  destruct_eq (x = l0); subst; updates...
  eapply_anywhere getVal_add; steps...
  right; split...
Qed.

(** Decidability of reachability *)

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

(** A path in an updated store either goes through the new value or was already valid in the un-updated store*)
Lemma rch_asgn_split :
  forall σ C ω f l0 l1,
    getObj σ l0 = Some (C, ω) ->
    forall l l' σ',
      σ' ⊨ l ⇝ l' ->
      σ' = [l0 ↦ (C, [f ↦ l1] ω)] σ ->
      (σ ⊨ l ⇝ l') \/ ((σ ⊨ l ⇝ l0) /\ (σ ⊨ l1 ⇝ l')).
Proof with (eauto with rch).
  intros.
  (* apply rch_iff_rch_tr in H0 as [tr H0]. *)
  induction H0; subst; updates...
  - destruct_eq (l0 = l2); subst; updates...
    destruct_eq (f = f0); subst; updates...
    right; split...
  - intuition auto...
    + right; split...
    + right; split...
Qed.



(** ** Assignment results *)


(* Lemma split_or {X} (l : list X) (P Q : X -> Prop) : *)
(*   (forall x, List.In x l -> (P x \/ Q x)) -> *)
(*   (exists x, List.In x l /\ P x) \/ (forall x, List.In x l -> Q x). *)
(* Proof. *)
(*   induction l; intros. *)
(*   - right; intros; inversion H0. *)
(*   - destruct (H a) as [HP | HQ]; [simpl; eauto | | ]. *)
(*     + left; exists a; simpl; eauto. *)
(*     + destruct IHl as [[x0 [Hin HP]] | HQ2]; eauto. *)
(*       * intros y. specialize (H y). *)
(*         intros. *)
(*         apply H; simpl; eauto. *)
(*       * left. exists x0; split; simpl; eauto. *)
(*       * right; intros. *)
(*         destruct H0; subst; eauto. *)
(* Qed. *)

(* Lemma In_tail: *)
(*   forall (X: Type) (l1 l2: list X) x, *)
(*     (forall y, List.In y l1 -> List.In y (x::l2)) -> *)
(*     (List.In x l1) \/ (forall y, List.In y l1 -> List.In y l2). *)
(* Proof. *)
(*   intros. *)
(*   pose proof (split_or l1 (fun y => x=y) (fun y => List.In y l2)). *)
(*   simpl in H0, H. *)
(*   apply H0 in H as [[y [H1 H2]] | H1]; subst; eauto. *)
(* Qed. *)


(* Theorem pigeonhole_principle: *)
(*   forall (X:Type) (l1 l2:list X), *)
(*     length l2 < length l1 -> *)
(*     (forall x, List.In x l1 -> List.In x l2) -> *)
(*     ~ NoDup l1. *)
(* Proof. *)
(*   induction l1 as [|x l1 IH]. *)
(*   - intros. *)
(*     inversion H. *)
(*   - intros. *)
(*     pose proof (H0 x) as H1; simpl; eauto. *)
(*     apply in_split in H1 as [l3 [l4 H1]]; simpl; eauto. *)
(*     specialize (IH (l3++l4)). *)
(*     subst. *)
(*     repeat rewrite app_length in H || simpl in H. *)
(*     repeat rewrite app_length in IH || simpl in IH. *)
(*     remember (l3++l4) as l2'. *)
(*     assert (forall y, List.In y l1 -> List.In y (x::l2')). *)
(*     + intros. subst. *)
(*       specialize (H0 y). *)
(*       simpl in *. steps. *)
(*       rewrite in_app_iff in H0. *)
(*       rewrite in_app_iff. steps. *)
(*     + intros HD. inverts HD. *)
(*       apply In_tail in H1 as [H1 | H1]; eauto using NoDup. *)
(*       apply IH; eauto with lia. *)
(* Qed. *)

(* Import PeanoNat.Nat. *)

(* Fixpoint reachabilityb n σ l l' := *)
(*   (eqb l l' && ltb l (dom σ)) *)
(*   || match getObj σ l with *)
(*     | Some (C, ω) => existsb (eqb l') ω && ltb l' (dom σ) *)
(*     | None => false *)
(*     end *)
(*   || match n with *)
(*     | 0   => false *)
(*     | S n => existsb (fun l0 => (reachabilityb n σ l l0) && (reachabilityb n σ l0 l')) (seq 0 (dom σ)) *)
(*     end. *)

(* Lemma reachabilityb_monotonicity: *)
(*   forall n1 n2 σ l l', *)
(*     n1 <= n2 -> *)
(*     reachabilityb n1 σ l l' -> *)
(*     reachabilityb n2 σ l l'. *)
(* Proof with (bools; eauto with lia). *)
(*   intros n1 n2. gen n1. *)
(*   induction n2; simpl in *; intros... *)
(*   - assert (n1 = 0) by lia; subst. *)
(*     simpl in H0... *)
(*   - apply Bool.orb_true_iff. *)
(*     destruct n1; simpl in *. *)
(*     + apply Bool.orb_true_iff in H0; steps. *)
(*     + apply Bool.orb_true_iff in H0 as [|]... *)
(*       right. *)
(*       apply existsb_exists in H0 as [x [? ?]]. *)
(*       apply existsb_exists; exists x; splits... *)
(*       flatten. *)
(*       split; eapply IHn2 with (n1 := n1)... *)
(* Qed. *)

(* Lemma reachabilityb_reachability: *)
(*   forall n σ l l', *)
(*     reachabilityb n σ l l' = true -> σ ⊨ l ⇝ l'. *)
(* Proof with (bools; eauto with rch lia). *)
(*   induction n; simpl; intros... *)
(*   - destruct H as [[[Heq Hlt]|]|]; try discriminate. *)
(*     + rewrite eqb_eq in Heq. subst. *)
(*       rewrite ltb_lt in Hlt... *)
(*     + destruct (getObj σ l) as [[C ω]|] eqn:?; [|discriminate]... *)
(*       destruct H as [Hex Hlt]. *)
(*       apply existsb_exists in Hex as [x [ ]]. *)
(*       rewrite eqb_eq in H0. subst. *)
(*       apply In_nth_error in H as [f ?]. *)
(*       apply ltb_lt in Hlt. *)
(*       eapply rch_step... *)
(*   - destruct H as [[[Heq Hlt]|]|]. *)
(*     + rewrite eqb_eq in Heq. subst. *)
(*       rewrite ltb_lt in Hlt... *)
(*     + destruct (getObj σ l) as [[C ω]|] eqn:?; [|discriminate]... *)
(*       destruct H as [Hex Hlt]. *)
(*       apply existsb_exists in Hex as [x [ ]]. *)
(*       rewrite eqb_eq in H0. subst. *)
(*       apply In_nth_error in H as [f ?]. *)
(*       apply ltb_lt in Hlt. *)
(*       eapply rch_step... *)
(*     + apply existsb_exists in H as [l0 [H__l0 ?]]. *)
(*       apply andb_prop in H as [ ]. *)
(*       apply rch_trans_n with l0... *)
(* Qed. *)
(* Local Hint Resolve reachabilityb_reachability: rch_t. *)

(* Lemma reachability_trace_reachabilityb: *)
(*   forall σ l l' tr, *)
(*     reachability_trace σ l l' tr -> reachabilityb (length tr) σ l l'. *)
(* Proof with (bools; eauto with lia rch_t rch). *)
(*   intros. *)
(*   induction H; simpl... *)
(*   - apply Bool.orb_true_iff. left. *)
(*     apply Bool.orb_true_iff. left. *)
(*     apply andb_true_intro; split. *)
(*     rewrite eqb_eq... *)
(*     rewrite ltb_lt... *)
(*   - apply Bool.orb_true_iff. left. *)
(*     apply Bool.orb_true_iff. right. *)
(*     rewrite H. *)
(*     apply andb_true_intro; split. *)
(*     apply existsb_exists. exists l'; split. *)
(*     eapply nth_error_In, H0. *)
(*     rewrite eqb_eq... *)
(*     rewrite ltb_lt... *)
(*   - remember (dom t1) as n1. *)
(*     remember (dom t2) as n2. *)
(*     rewrite app_length; simpl. *)
(*     rewrite -Heqn1 -Heqn2 -plus_n_Sm. simpl. *)
(*     apply Bool.orb_true_intro. right. *)
(*     apply existsb_exists. exists l1. split; simpl. *)
(*     + apply in_seq; simpl; split... *)
(*     + apply andb_true_intro; split; *)
(*         eapply reachabilityb_monotonicity ; try eassumption... *)
(* Qed. *)
(* Local Hint Resolve reachability_trace_reachabilityb : rch_t. *)

(* Theorem reachability_dec: *)
(*   forall σ l l', *)
(*     {σ ⊨ l ⇝ l'} + {~ σ ⊨ l ⇝ l'}. *)
(* Proof with (eauto with rch rch_t lia). *)
(*   intros. *)
(*   assert (reflect (σ ⊨ l ⇝ l') (reachabilityb (dom σ) σ l l')); [| inverts H; eauto]. *)
(*   assert ((σ ⊨ l ⇝ l') <-> exists tr, reachability_trace σ l l' tr /\ (length tr <= dom σ)). *)
(*   - split; intros. *)
(*     + apply reachability_trace_reachability in H as [tr0 H]. *)
(*       apply reachability_trace_NoDup in H as [tr [H Hdup]]. *)
(*       exists tr; split... *)
(*       assert (dom σ < dom tr \/ dom tr <= dom σ) as [|] by lia... *)
(*       assert (dom σ = dom (seq 0 (dom σ))); try rewrite seq_length... *)
(*       rewrite H1 in H0. *)
(*       eapply pigeonhole_principle in H0. exfalso... *)
(*       intros. apply in_seq; simpl; split... *)
(*       pose proof (reachability_trace_is_reachable σ l l' tr x) as [(t0 & t1 & ? & ? & _) _]... *)
(*     + destruct H as [tr [ ]]... *)
(*   - destruct (reachabilityb (dom σ) σ l l') eqn:Hb. *)
(*     + apply Bool.ReflectT... *)
(*     + apply Bool.ReflectF. *)
(*       intros Hf. apply H in Hf as [tr [Hf Htr]]. *)
(*       apply reachability_trace_reachabilityb, reachabilityb_monotonicity with (n2 := dom σ) in Hf... *)
(* Qed. *)

(* End rch_decidability. *)

(* Check reachability_dec. *)
