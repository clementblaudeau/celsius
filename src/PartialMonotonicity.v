(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the notion of partial monotonicity between stores. The idea behind partial monotonicity is simple: objects that are being initialized (not warm already) can only get "warmer": the number of initialized fields can only increase. Between two stores [σ] and [σ'], it means that all objects in [σ] have more initialized fields in [σ']; it does not states anything about new objects that [σ'] can have. *)

From Celsius Require Export Semantics.
Require Import ssreflect ssrbool List Psatz Coq.Program.Tactics.
Import ListNotations.
Open Scope nat_scope.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc).

(** ** Definitions and notations *)
Definition partial_monotonicity σ σ' :=
  forall l C ω, getObj σ l = Some(C, ω) -> exists ω', getObj σ' l = Some(C, ω') /\ dom ω <= dom ω'.
Notation "s ⪯ s'" := (partial_monotonicity s s') (at level 60).

Local Hint Unfold partial_monotonicity: pM.

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
Lemma pM_assign:
  forall σ l C ω f v,
    getObj σ l = Some (C, ω) ->
    σ ⪯ [l ↦ (C, [f ↦ v]ω)]σ.
Proof.
  autounfold with pM notations.
  intros.
  lets: getObj_dom H.
  destruct_eq (l = l0); subst;
    updates; cross_rewrites; auto;
    eexists; eauto with updates.
Qed.
Global Hint Resolve pM_assign: pM.

Lemma pM_assign_new:
  forall σ σ' l x v,
    assign_new l x v σ = Some σ' ->
    σ ⪯ σ'.
Proof.
  autounfold with pM notations. unfold assign_new.
  intros.
  lets: getObj_dom H0.
  destruct (getObj σ l) as [[C' ω'] |] eqn:?.
  + destruct (Nat.eqb x (dom ω')); inverts H;
    destruct_eq (l = l0); subst;
    updates; cross_rewrites; auto;
      eexists; split; eauto; updates; try lia.
  + inverts H.
Qed.
Global Hint Resolve pM_assign_new: pM.

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
  (forall e σ ρ ψ v σ',
      ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> σ ⪯ σ') /\
    (forall el σ ρ ψ vl σ',
        ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') -> σ ⪯ σ') /\
    (forall C ψ x ρ σ σ',
        initP C ψ x ρ σ σ' -> σ ⪯ σ').
Proof with (eauto with pM updates lia).
  apply evalP_multi_ind;
    unfold assign; intros;
    repeat destruct_match;
    flatten; pM_trans; try discriminate...
Qed.

Corollary pM_theorem_expr:
  forall e σ ρ ψ v σ',
      ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> σ ⪯ σ'.
Proof.
  apply pM_theorem.
Qed.
Global Hint Resolve pM_theorem_expr: pM.

Corollary pM_theorem_list:
  forall el σ ρ ψ vl σ',
      ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') -> σ ⪯ σ'.
Proof.
  apply pM_theorem.
Qed.
Global Hint Resolve pM_theorem_list: pM.

Corollary pM_theorem_init:
  forall C ψ x ρ σ σ',
      initP C ψ x ρ σ σ' -> σ ⪯ σ'.
Proof.
  apply pM_theorem.
Qed.
Global Hint Resolve pM_theorem_init: pM.
