(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the notion of partial monotonicity between stores. The idea behind partial monotonicity is simple: objects that are being initialized (not warm already) can only get "warmer": the number of initialized fields can only increase. Between two stores [σ] and [σ'], it means that all objects in [σ] have more initialized fields in [σ']; it does not states anything about new objects that [σ'] can have. *)

From Celsius Require Export Semantics.
Require Import ssreflect ssrbool List Psatz Coq.Program.Tactics.
Import ListNotations.
Open Scope nat_scope.

(** ** Definitions and notations *)
Definition partial_monotonicity σ σ' :=
  forall l C ω, getObj σ l = Some(C, ω) -> exists ω', getObj σ' l = Some(C, ω') /\ dom ω <= dom ω'.
Notation "s ⪯ s'" := (partial_monotonicity s s') (at level 60).
Definition exact_monotonicity σ σ' :=
  forall l C ω, getObj σ l = Some(C, ω) -> exists ω', getObj σ' l = Some(C, ω') /\ dom ω = dom ω'.
Notation "s ⪳ s'" := (exact_monotonicity s s') (at level 60).

Local Hint Unfold partial_monotonicity: pM.
Local Hint Unfold exact_monotonicity: pM.
Implicit Type σ: Store.

(** ** Basic results on partial monotonicity*)
(** The relation is trivially reflexive and transitive *)
Lemma pM_refl: forall σ,
    σ ⪯ σ.
Proof. eauto with pM. Qed.
Global Hint Resolve pM_refl: pM.

Lemma pM_trans : forall σ1 σ2 σ3,
    σ1 ⪯ σ2 ->
    σ2 ⪯ σ3 ->
    σ1 ⪯ σ3.
Proof.
  unfold partial_monotonicity; intros.
  specialize (H l C ω); steps.
  specialize (H0 l C ω'); steps; eauto with pM lia.
Qed.
Global Hint Resolve pM_trans: pM.

Ltac pM_trans :=
  repeat match goal with
         | H:_ |- ?σ ⪯ ?σ => apply pM_refl
         | H: ?σ1 ⪯ ?σ2 |- ?σ1 ⪯ ?σ3 => apply pM_trans with σ2 ; [ assumption | ]
         | H: ?σ2 ⪯ ?σ3 |- ?σ1 ⪯ ?σ3 => apply pM_trans with σ2 ; [ | assumption ]
         end.
Global Hint Extern 1 => pM_trans: pM.


(** We have a result on the store sizes *)
Lemma pM_domains:
  forall σ σ',
    σ ⪯ σ' -> dom σ <= dom σ'.
Proof.
  autounfold; unfold partial_monotonicity; intros.
  destruct σ eqn:Σ; simpl; [lia |].
  destruct o as [C ω].
  specialize (H (dom s)).
  destruct (getObj ((C, ω)::s) (dom s)) eqn: H__e.
  - destruct o as [D ω'].
    apply H in H__e; steps.
    apply getObj_dom in H1; auto.
  - unfold getObj in H__e.
    apply nth_error_None in H__e.
    simpl in H__e; lia.
Qed.
Global Hint Resolve pM_domains: pM.


(** ** Main Monotonicity result *)
(** We start with two technical results on partial monotonicity for assignment (update) and fresh location *)
Lemma pM_assignment :
  forall σ l C (ω ω': Env),
    getObj σ l = Some (C, ω) ->
    length ω <= length ω' ->
    σ ⪯ [l ↦ (C, ω')]σ.
Proof.
  autounfold with pM notations.
  intros.
  destruct_eq (l = l0); subst;
    repeat rewrite_any;
    rewrite getObj_update1 || rewrite getObj_update2;
    eauto using getObj_dom.
  steps. eexists; split; eauto.
Qed.
Global Hint Resolve pM_assignment: pM.

Lemma pM_freshness :
  forall σ c ρ,
    σ ⪯ (σ ++ [(c, ρ)]).
Proof.
  autounfold with notations pM. unfold getObj; intros.
  exists ω; steps.
  rewrite nth_error_app1; eauto using getObj_dom.
Qed.
Global Hint Resolve pM_freshness: pM.

(** Then we have the main result *)
Theorem pM_theorem:
  forall e σ σ' ρ ψ v,
      ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> σ ⪯ σ'.
Proof with (eauto with pM updates lia).
  intros.
  induction H using evalP_ind2 with
    (Pl := fun _ σ _ _ _ σ' _ => σ ⪯ σ')
    (Pin := fun _ _ _ _ σ σ' _ => σ ⪯ σ');
    unfold assign, assign_new in *;
    repeat destruct_match;
    flatten; pM_trans ...
Qed.
Global Hint Resolve pM_theorem: pM.

Corollary pM_theorem_list:
  forall el σ σ' ρ ψ vl,
      ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') -> σ ⪯ σ'.
Proof with (eauto with pM updates lia).
  intros.
  induction H ...
Qed.
Global Hint Resolve pM_theorem_list: pM.

Corollary pM_theorem_init:
  forall C fls ψ ρ σ σ',
      initP C fls ψ ρ σ σ' -> σ ⪯ σ'.
Proof with (eauto with pM updates lia).
  intros.
  induction H;
    unfold assign, assign_new in *; ground ...
  eapply pM_theorem in H ...
Qed.
Global Hint Resolve pM_theorem_init: pM.


(** ** Exact monotonicity results *)

(** ** Basic results on partial monotonicity*)
(** The relation is trivially reflexive and transitive *)
Lemma eM_refl: forall σ,
    σ ⪳ σ.
Proof. eauto with pM. Qed.
Global Hint Resolve eM_refl: pM.

Lemma eM_trans : forall σ1 σ2 σ3,
    σ1 ⪳ σ2 ->
    σ2 ⪳ σ3 ->
    σ1 ⪳ σ3.
Proof.
  unfold exact_monotonicity; intros.
  specialize (H l C ω); steps.
  specialize (H0 l C ω'); steps; eauto with pM lia.
Qed.
Global Hint Resolve eM_trans: pM.

Ltac eM_trans :=
  repeat match goal with
         | H:_ |- ?σ ⪳ ?σ => apply eM_refl
         | H: ?σ1 ⪳ ?σ2 |- ?σ1 ⪳ ?σ3 => apply eM_trans with σ2 ; [ assumption | ]
         | H: ?σ2 ⪳ ?σ3 |- ?σ1 ⪳ ?σ3 => apply eM_trans with σ2 ; [ | assumption ]
         end.
Global Hint Extern 1 => eM_trans: pM.


(** We have a result on the store sizes *)
Lemma eM_domains:
  forall σ σ',
    σ ⪳ σ' -> dom σ <= dom σ'.
Proof.
  autounfold; unfold exact_monotonicity; intros.
  destruct σ eqn:Σ; simpl; [lia |].
  destruct o as [C ω].
  specialize (H (dom s)).
  destruct (getObj ((C, ω)::s) (dom s)) eqn: H__e.
  - destruct o as [D ω'].
    apply H in H__e; steps.
    apply getObj_dom in H1; auto.
  - unfold getObj in H__e.
    apply nth_error_None in H__e.
    simpl in H__e; lia.
Qed.
Global Hint Resolve eM_domains: pM.


(** ** Main Monotonicity result *)
(** We start with two technical results on partial monotonicity for assignment (update) and fresh location *)
Lemma eM_assignment :
  forall σ l C (ω ω': Env),
    getObj σ l = Some (C, ω) ->
    length ω = length ω' ->
    σ ⪳ [l ↦ (C, ω')]σ.
Proof.
  autounfold with pM notations.
  intros.
  destruct_eq (l = l0); subst;
    repeat rewrite_any;
    rewrite getObj_update1 || rewrite getObj_update2;
    eauto using getObj_dom.
  steps. eexists; split; eauto.
Qed.
Global Hint Resolve eM_assignment: pM.

Lemma eM_freshness :
  forall σ c ρ,
    σ ⪳ (σ ++ [(c, ρ)]).
Proof.
  autounfold with notations pM. unfold getObj; intros.
  exists ω; steps.
  rewrite nth_error_app1; eauto using getObj_dom.
Qed.
Global Hint Resolve eM_freshness: pM.

(** Then we have the main result *)
Theorem eM_theorem:
  forall e σ σ' ρ ψ v,
      ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> σ ⪳ σ'.
Proof with (update_dom; eauto 3 with pM updates lia).
  intros.
  induction H using evalP_ind2 with
    (Pl := fun _ σ _ _ _ σ' _ => σ ⪳ σ')
    (Pin := fun C flds ψ _  σ σ' _ =>
              forall ω Args Flds Mtds,
                ct C = class Args Flds Mtds ->
                getObj σ ψ = Some(C, ω) ->
                dom ω + dom flds = dom Flds ->
                σ ⪳ [ψ ↦ (C, repeat 0 (dom ω) )]σ');
    unfold assign, assign_new in *;
    repeat destruct_match; eval_dom;
    flatten; pM_trans ...
  - (* e_new *)
    specialize (IHevalP0 [] _ _ _ H__ct (getObj_last _ _ _) ltac:(simpl;lia)).
    lets: eM_domains IHevalP0...
    intros l D ω H__get; steps.
    lets [ω' [H__get1 ? ]] : IHevalP H__get; eauto.
    lets : getObj_dom H__get1.
    specialize (IHevalP0 l D ω' ltac:(rewrite getObj_last2; eauto using Lt.lt_le_trans with lia)) as [ω'' [ ]].
    exists ω''; split ...
    getObj_update; steps; try lia.
  - intros. simpl in H1.
    intros l; steps.
    destruct_eq (l = I).
    + exists (repeat 0 dom ω). subst.
      rewrite getObj_update1 ...
      rewrite H0 in H2; steps.
      rewrite repeat_length. reflexivity.
    + exists ω0.
      rewrite getObj_update2...
  - update_dom; steps.
    intros l D ω' H__get; steps.
    lets [ω'' [H__get1 ? ]] : IHevalP H3; eauto.
    rewrite matched in H__get1; steps.
    lets: getObj_dom matched.
    lets: eM_domains IHevalP.
    specialize (IHevalP0 (ω''++[v]) _ _ _ H2
                         ltac: (eapply getObj_update1; eauto with lia)
                                 ltac:(rewrite app_length; simpl; lia)).
    lets [ω''' [ ]]: IHevalP l H__get.
    destruct_eq (l = I); subst.
    + rewrite H8 in matched; rewrite H__get in H3; steps.
      exists (repeat 0 dom ω).
      rewrite getObj_update1; try split ...
      rewrite repeat_length. reflexivity.
    + specialize (IHevalP0 l D ω''' ltac:(rewrite getObj_update2; eauto)) as [ω'''' [ ] ]...
      exists ω''''.
      getObj_update; steps; eauto; try lia.
      rewrite getObj_update2 ...
Qed.
Global Hint Resolve eM_theorem: pM.

Corollary eM_theorem_list:
  forall el σ σ' ρ ψ vl,
      ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') -> σ ⪳ σ'.
Proof with (eauto with pM updates lia).
  intros.
  induction H ...
Qed.
Global Hint Resolve eM_theorem_list: pM.

(** Exact monotonic stores keep objects warm *)
From Celsius Require Import Reachability.
Lemma eM_warm_monotone:
  forall σ σ' (l: Loc),
    σ ⪳ σ' ->
    σ  ⊨ l : warm ->
    σ' ⊨ l : warm.
Proof.
  autounfold with pM core notations. unfold reachable_warm.
  steps.
  lets [?ω' [ ] ] : H H1.
  repeat eexists; eauto.
Qed.
